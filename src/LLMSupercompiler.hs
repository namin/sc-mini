{-# LANGUAGE OverloadedStrings #-}

module LLMSupercompiler
  ( supercompileIO
  , supercompileIOWithTypes
  , supercompilePure
  ) where

import Data
import DataUtil
import DataIO
import Driving
import Folding
import Generator
import Deforester (simplify)
import Supercompiler (addPropagation)
import Bedrock
import Types (TypeEnv)
import LeanEmbed (embedConjecture)
import LeanCheck (LeanProject, projDir, Verdict(..), setupProject, verify, teardownProject)
import LeanProver (tryAuto)

import Data.List (intercalate, isPrefixOf)
import Data.IORef
import Control.Exception (try, SomeException)
import System.IO (hPutStrLn, stderr)

maxLLMCalls :: Int
maxLLMCalls = 10

-- A Whistle decides what to do when the homeomorphic-embedding check
-- fires: given (ancestor, freshName, current, nameSupply), produce the
-- expression the supercompiler should drive next. Returns IO so it can
-- consult the LLM and/or Lean.
type Whistle = Conf -> Name -> Conf -> NameSupply -> IO Conf

-- Existing entry point: LLM proposes generalizations, no verification.
supercompileIO :: Task -> IO Task
supercompileIO (e, p) = do
  counter <- newIORef (0 :: Int)
  let w = mkUnverifiedWhistle counter p
  tree <- bftIO w (addPropagation $ driveMachine p) nameSupply [] e
  return $ residuate $ simplify $ foldTree tree

-- New entry point: LLM proposes generalizations and either auto-prove or
-- LLM-supplied Lean proof must verify before we accept them. On any
-- verification failure path we fall back to msgToLet.
supercompileIOWithTypes :: TypeEnv -> Task -> IO Task
supercompileIOWithTypes env (e, p) = do
  counter <- newIORef (0 :: Int)
  proj <- setupProject env p
  hPutStrLn stderr $ "[lean] proofs dir: " ++ projDir proj
  let w = mkVerifiedWhistle counter env p proj
  tree <- bftIO w (addPropagation $ driveMachine p) nameSupply [] e
  let result = residuate $ simplify $ foldTree tree
  teardownProject proj
  return result

supercompilePure :: Task -> Task
supercompilePure (e, p) =
  residuate $ simplify $ foldTree $ bftPure (addPropagation $ driveMachine p) nameSupply [] e

-- Pure version with homeomorphic embedding
bftPure :: Machine Conf -> NameSupply -> [Conf] -> Conf -> Tree Conf
bftPure d (n:ns) hist e
  | whistleCandidate e, Just _ <- findEmbedding hist e =
      bftPure d ns hist (classicalGeneralize n e)
bftPure d ns hist t = case d ns t of
  Decompose ds -> Node t $ Decompose $ map (bftPure d ns hist') ds
  Transient e  -> Node t $ Transient $ bftPure d ns hist' e
  Stop         -> Node t Stop
  Variants cs  -> Node t $ Variants [(c, bftPure d (unused c ns) hist' e) | (c, e) <- cs]
  where hist' = if isCall t then t : hist else hist

-- IO version with HE whistle. The Whistle parameter decides what
-- generalized expression to use when HE fires; this layer is purely
-- structural and doesn't know about LLM or Lean.
bftIO :: Whistle -> Machine Conf -> NameSupply -> [Conf] -> Conf -> IO (Tree Conf)
bftIO w d (n:ns) hist e
  | whistleCandidate e, Just anc <- findEmbedding hist e = do
      let hist' = filter (/= anc) hist
      hPutStrLn stderr "  [whistle] HE detected"
      hPutStrLn stderr $ "    ancestor:  " ++ showSLL anc
      hPutStrLn stderr $ "    current:   " ++ showSLL e
      gen <- w anc n e ns
      bftIO w d ns hist' gen
bftIO w d ns hist t = case d ns t of
  Decompose ds -> do
    cs <- mapM (bftIO w d ns hist') ds
    return $ Node t $ Decompose cs
  Transient e -> do
    c <- bftIO w d ns hist' e
    return $ Node t $ Transient c
  Stop -> return $ Node t Stop
  Variants cs -> do
    cs' <- sequence [(,) c <$> bftIO w d (unused c ns) hist' e | (c, e) <- cs]
    return $ Node t $ Variants cs'
  where hist' = if isCall t then t : hist else hist

-- Whistle for the unverified path: ask the LLM, accept whatever it says
-- (with classical fallback on parse/network failure or budget exhaustion).
mkUnverifiedWhistle :: IORef Int -> Program -> Whistle
mkUnverifiedWhistle counter prog anc n e _ = do
  calls <- readIORef counter
  if calls >= maxLLMCalls
    then do
      hPutStrLn stderr "  [whistle] budget exhausted, using classical"
      return (classicalGeneralize n e)
    else llmGeneralize counter prog anc n e

-- Whistle for the verified path: ask the LLM, then auto-prove; if that
-- fails, ask the LLM for a proof body and verify that; on any persistent
-- failure (budget, proof, or absent response), fall back to classical
-- generalization, which is what the pure path uses and is known to
-- converge structurally.
mkVerifiedWhistle :: IORef Int -> TypeEnv -> Program -> LeanProject -> Whistle
mkVerifiedWhistle counter env prog proj anc n e _ = do
  calls <- readIORef counter
  if calls >= maxLLMCalls
    then do
      hPutStrLn stderr "  [whistle] budget exhausted, using classical"
      return (classicalGeneralize n e)
    else do
      gen <- llmGeneralize counter prog anc n e
      v <- tryAuto env prog proj e gen
      case v of
        Ok -> do
          hPutStrLn stderr "  [verify] auto-prove Ok"
          return gen
        Failed s -> do
          hPutStrLn stderr "  [verify] auto-prove Failed; asking LLM for proof"
          mProof <- llmProveBody counter env prog e gen s
          case mProof of
            Nothing -> do
              hPutStrLn stderr "  [verify] no proof available; falling back to classical"
              return (classicalGeneralize n e)
            Just proof -> do
              v2 <- verify proj (embedConjecture env prog e gen proof)
              case v2 of
                Ok -> do
                  hPutStrLn stderr "  [verify] LLM proof Ok"
                  return gen
                Failed s2 -> do
                  hPutStrLn stderr $ "  [verify] LLM proof Failed: "
                                     ++ take 200 s2
                  return (classicalGeneralize n e)

whistleCandidate :: Expr -> Bool
whistleCandidate (FCall _ args) = not (all isVar args)
whistleCandidate (GCall _ args) = not (all isVar args)
whistleCandidate _ = False

-- Find the first ancestor that homeomorphically embeds in the current term
findEmbedding :: [Conf] -> Conf -> Maybe Conf
findEmbedding [] _ = Nothing
findEmbedding (a:as) e
  | homeEmbed a e = Just a
  | otherwise = findEmbedding as e

-- Ask the LLM to generalize given the ancestor/descendant pair. On any
-- failure (network, parse, malformed reply) we fall through to classical
-- generalization, the same one the pure path uses.
llmGeneralize :: IORef Int -> Program -> Conf -> Name -> Conf -> IO Conf
llmGeneralize counter prog ancestor freshName expr = do
  modifyIORef' counter (+1)
  calls <- readIORef counter
  let prompt = buildPrompt prog ancestor expr freshName
      fallback = classicalGeneralize freshName expr
  hPutStrLn stderr $ "  [llm] call #" ++ show calls
  result <- try (chat prompt) :: IO (Either SomeException String)
  case result of
    Left err -> do
      hPutStrLn stderr $ "  [llm] error: " ++ show err ++ ", falling back to classical"
      return fallback
    Right response -> do
      hPutStrLn stderr $ "  [llm] response: " ++ take 200 response
      case tryParse response of
        Just parsed -> do
          hPutStrLn stderr $ "  [llm] parsed: " ++ showSLL parsed
          return parsed
        Nothing -> do
          hPutStrLn stderr "  [llm] parse failed, falling back to classical"
          return fallback

-- Ask the LLM for a Lean proof body. Counts against the same budget as
-- generalization calls. Returns the parsed `by ...` block or Nothing.
llmProveBody :: IORef Int -> TypeEnv -> Program -> Conf -> Conf -> String -> IO (Maybe String)
llmProveBody counter env prog e gen autoFailure = do
  modifyIORef' counter (+1)
  calls <- readIORef counter
  let prompt = buildProofPrompt env prog e gen autoFailure
  hPutStrLn stderr $ "  [llm-proof] call #" ++ show calls
  result <- try (chat prompt) :: IO (Either SomeException String)
  case result of
    Left err -> do
      hPutStrLn stderr $ "  [llm-proof] error: " ++ show err
      return Nothing
    Right response -> do
      let proof = extractProofBody response
      hPutStrLn stderr $ "  [llm-proof] body: " ++ take 200 proof
      return (Just proof)

-- Extract the `by …` block from the LLM response. Tolerates markdown
-- fencing and a brief preamble; drops any trailing prose or fences.
-- If no `by ` token is found, hands the cleaned text to Lean as-is and
-- lets the failure trigger the msg fallback.
extractProofBody :: String -> String
extractProofBody resp =
  stopAtFence (dropToBy (stripMarkdown (strip resp)))
  where
    dropToBy s
      | "by " `isPrefixOf` s = s
      | "by\n" `isPrefixOf` s = s
      | null s = s
      | otherwise = dropToBy (drop 1 s)

    stopAtFence ('`':'`':'`':_) = ""
    stopAtFence (c:rest)        = c : stopAtFence rest
    stopAtFence []              = []

buildProofPrompt :: TypeEnv -> Program -> Conf -> Conf -> String -> String
buildProofPrompt env prog e gen autoFailure = unlines
  [ "You are a Lean 4 prover. The supercompiler proposed a generalization"
  , "of the form  e ≡ e'  but the auto-prove step (simp_all with the"
  , "program's equation lemmas) could not discharge it."
  , ""
  , "We need a Lean 4 tactic block that proves this theorem:"
  , ""
  , embedConjecture env prog e gen "<YOUR PROOF HERE>"
  , ""
  , "The function names " ++ funList ++ " are the program's definitions"
  , "and their equation lemmas are available to simp."
  , ""
  , "Auto-prove output (for context — these are the errors we must avoid):"
  , autoFailure
  , ""
  , "Reply with ONLY the proof body — a single Lean 4 expression starting"
  , "with `by `. Use only core Lean 4 tactics (no Mathlib). Common"
  , "ingredients: intros, simp_all [<defs>], induction <var>, cases <var>,"
  , "<;> (sequence-all), rfl."
  , ""
  , "Example: by intros; induction x <;> simp_all [gAdd, gMult]"
  ]
  where
    funList = intercalate ", " (proverFunNames prog)

proverFunNames :: Program -> [Name]
proverFunNames (Program fs gs) =
  [n | FDef n _ _ <- fs] ++ [n | GDef n _ _ _ <- gs]

buildPrompt :: Program -> Conf -> Conf -> Name -> String
buildPrompt prog ancestor expr freshName =
  unlines
    [ "You are a supercompiler for SLL (Simple Lazy Language)."
    , ""
    , "SLL syntax (use EXACTLY this in your reply):"
    , "  Variables: x, y, v1, v2, ..."
    , "  Constructors: Name(args) e.g. S(x), Z(), Cons(x, xs)"
    , "  F-calls: fName(args) — names start with 'f'"
    , "  G-calls: gName(args) — names start with 'g'"
    , "  Let: let v = e1 in e2"
    , ""
    , "Program:"
    , showSLLProgram prog
    , ""
    , "The homeomorphic embedding whistle has fired. The current expression"
    , "is a structurally larger version of an ancestor in the process tree:"
    , ""
    , "  ancestor: " ++ showSLL ancestor
    , "  current:  " ++ showSLL expr
    , ""
    , "The current term has GROWN compared to the ancestor. To ensure"
    , "termination, extract a subexpression into a let-binding using"
    , "fresh variable '" ++ freshName ++ "'."
    , ""
    , "The goal: after extracting, the remaining call should be similar"
    , "enough to the ancestor that it can FOLD BACK (creating a loop"
    , "in the residual program instead of infinite unfolding)."
    , ""
    , "Look at what changed between ancestor and current — the NEW"
    , "subexpressions are what should be extracted."
    , ""
    , "Reply with ONLY the let-expression. No explanation."
    , "Example: let " ++ freshName ++ " = gAdd(x, y) in gMult(" ++ freshName ++ ", z)"
    ]

showSLLProgram :: Program -> String
showSLLProgram (Program fs gs) = intercalate "\n" $ map sf fs ++ map sg gs
  where
    sf (FDef n args body) = n ++ "(" ++ intercalate ", " args ++ ") = " ++ showSLL body ++ ";"
    sg (GDef n (Pat cn cvs) args body) =
      n ++ "(" ++ cn ++ "(" ++ intercalate ", " cvs ++ ")" ++
      concatMap (", " ++) args ++ ") = " ++ showSLL body ++ ";"

tryParse :: String -> Maybe Conf
tryParse response =
  let cleaned = stripMarkdown $ strip response
      attempts = [cleaned] ++ extractCodeBlock response
  in firstJust (map safeParse attempts)

stripMarkdown :: String -> String
stripMarkdown s
  | take 3 s == "```" = stripMarkdown $ unlines $ init $ tail $ lines s
  | otherwise = s

extractCodeBlock :: String -> [String]
extractCodeBlock s =
  case break (== '`') s of
    (_, '`':'`':'`':rest) ->
      case break (== '`') (dropWhile (/= '\n') rest) of
        (code, _) -> [strip code]
    _ -> []

safeParse :: String -> Maybe Conf
safeParse s = case [(e, r) | (e, r) <- reads s, all isSp r] of
  (expr, _):_ -> Just expr
  _           -> Nothing
  where isSp c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs

strip :: String -> String
strip = reverse . dropWhile (== '\n') . reverse . dropWhile (== '\n')

-- Convert msg result into a let-chain: let v1 = e1 in let v2 = e2 in gen
-- where gen is the generalized expression and the bindings come from
-- the substitution for the current (descendant) expression.
msgToLet :: NameSupply -> Expr -> Expr -> Expr
msgToLet ns current ancestor =
  let (gen, _, s2) = msg ns ancestor current
  in foldr (\(v, e) body -> Let (v, e) body) gen s2

classicalGeneralize :: Name -> Expr -> Expr
classicalGeneralize n (FCall f es) =
  Let (n, e) (FCall f es') where (e, es') = extractArg n es
classicalGeneralize n (GCall g es) =
  Let (n, e) (GCall g es') where (e, es') = extractArg n es
classicalGeneralize _ e = e

extractArg :: Name -> [Expr] -> (Expr, [Expr])
extractArg n es = (maxE, vs ++ Var n : ws) where
  maxE = maximumBy ecompare es
  ecompare x y = compare (eType x * size x) (eType y * size y)
  (vs, _ : ws) = break (maxE ==) es
  eType e = if isVar e then 0 else 1
  maximumBy f (x:xs) = foldl (\a b -> if f a b == LT then b else a) x xs
