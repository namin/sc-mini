{-# LANGUAGE OverloadedStrings #-}

-- Distillation pre-pass: ask the LLM for eureka lemmas about the input
-- task, verify them in Lean, and rewrite the task using verified lemmas
-- before driving begins. See DESIGN_LEAN.md "Distillation" for the
-- design rationale.
--
-- The structural rewrites the LLM proposes during driving (let
-- introductions) preserve operation count, so the LLM-supercompiled
-- residual matches the original program's runtime. Eureka lemmas are
-- assertions about *equivalence* — they change which expressions are
-- equal, not just how they're structured — and that's what enables real
-- speedups. This module is where the LLM gets to be brilliant about
-- semantics, not just structure.

module Distillation
  ( proposeLemma
  , verifyLemma
  , rewriteWith
  , distillTask
  , Bindings
  , unify
  ) where

import Data
import DataIO (showSLL)
import DataUtil ((//))
import Types
import Bedrock (chat)
import LeanEmbed (embedLemma)
import LeanCheck (LeanProject, Verdict(..), verify)

import Control.Exception (try, SomeException)
import Data.Char (isSpace)
import Data.IORef
import Data.List (isPrefixOf)
import System.IO (hPutStrLn, stderr)

-- =========================================================================
-- Pattern matching: lemma LHS against a candidate subexpression
-- =========================================================================

type Bindings = [(Name, Expr)]

-- Unify a lemma's LHS pattern against a candidate expression.
-- Variables in `pvars` are pattern variables (free, can match anything);
-- other vars must match the same Var literally. Returns the binding map
-- on success.
unify :: [Name] -> Expr -> Expr -> Maybe Bindings
unify pvars (Var v) e | v `elem` pvars = Just [(v, e)]
unify _     (Var v1) (Var v2) | v1 == v2 = Just []
unify pvars (Ctr n1 es1) (Ctr n2 es2)
  | n1 == n2 = unifyAll pvars es1 es2
unify pvars (FCall n1 es1) (FCall n2 es2)
  | n1 == n2 = unifyAll pvars es1 es2
unify pvars (GCall n1 es1) (GCall n2 es2)
  | n1 == n2 = unifyAll pvars es1 es2
unify _ _ _ = Nothing

unifyAll :: [Name] -> [Expr] -> [Expr] -> Maybe Bindings
unifyAll _ [] [] = Just []
unifyAll pvars (a:as) (b:bs) = do
  bA <- unify pvars a b
  bR <- unifyAll pvars as bs
  mergeBindings bA bR
unifyAll _ _ _ = Nothing

-- Merge two binding sets; reject inconsistencies (same pvar bound to
-- different terms).
mergeBindings :: Bindings -> Bindings -> Maybe Bindings
mergeBindings [] b2 = Just b2
mergeBindings ((v, e) : rest) b2 =
  case lookup v b2 of
    Just e' | e /= e' -> Nothing
    _                 -> mergeBindings rest (insertBind v e b2)
  where
    insertBind k x ((k', _) : kvs) | k == k' = (k, x) : kvs
    insertBind k x (kv : kvs)                = kv : insertBind k x kvs
    insertBind k x []                        = [(k, x)]

-- =========================================================================
-- Rewriter: try to apply a lemma to the topmost matching subexpression
-- =========================================================================

-- Top-down search for a subexpression matching the lemma's LHS.
-- Returns Just rewritten on first match, Nothing if the lemma doesn't
-- apply anywhere in `e`.
rewriteWith :: Lemma -> Expr -> Maybe Expr
rewriteWith lem e =
  case unify (map fst (lemmaForall lem)) (lemmaLhs lem) e of
    Just b  -> Just (lemmaRhs lem // b)
    Nothing -> tryChildren e
  where
    tryChildren (Ctr   n es)     = Ctr   n <$> tryList es
    tryChildren (FCall n es)     = FCall n <$> tryList es
    tryChildren (GCall n es)     = GCall n <$> tryList es
    tryChildren (Let (v, e1) e2) =
      case rewriteWith lem e1 of
        Just e1' -> Just (Let (v, e1') e2)
        Nothing  -> Let (v, e1) <$> rewriteWith lem e2
    tryChildren _                = Nothing

    tryList []     = Nothing
    tryList (x:xs) = case rewriteWith lem x of
      Just x' -> Just (x' : xs)
      Nothing -> (x:) <$> tryList xs

-- =========================================================================
-- LLM prompt: ask for one eureka lemma about the program + expression
-- =========================================================================

buildLemmaPrompt :: TypeEnv -> Program -> [Lemma] -> Expr -> String
buildLemmaPrompt env prog context e = unlines $
  [ "You are a supercompiler that's about to drive an SLL expression."
  , "Before driving starts, propose ONE eureka lemma about the program"
  , "that would simplify the expression. The lemma must be a"
  , "universally-quantified equation provable in Lean 4."
  , ""
  , "SLL syntax (use EXACTLY this in lhs/rhs):"
  , "  Variables: x, y, n, ..."
  , "  Constructors: Name(args) e.g. Z(), S(x), Cons(h, t)"
  , "  F-calls: fName(args) — names start with 'f'"
  , "  G-calls: gName(args) — names start with 'g'"
  , ""
  , "Program:"
  , showSLLProgramFull prog
  , ""
  , "Type declarations:"
  , showTypeDefs (typeDefs env)
  , ""
  , "Function signatures:"
  , showFunSigs (funSigs env)
  , ""
  ] ++ contextSection ++
  [ "Expression we will supercompile:"
  , "  " ++ showSLL e
  , ""
  , "Goal: a lemma whose LHS matches a subexpression of the expression"
  , "above, and whose RHS is structurally simpler (fewer function calls,"
  , "or replaces a complex computation with a variable). For instance,"
  , "if the program defines double and half, a useful lemma might be"
  , "`forall n, gHalf(gDouble(n)) = n`."
  , ""
  , "If the lemma you'd ideally state needs sub-lemmas to prove, propose"
  , "ONE of those sub-lemmas this turn — it will be verified and made"
  , "available as a rewrite rule in your next attempt. Building up a"
  , "chain of small, individually-provable lemmas is preferable to"
  , "proposing one big lemma whose proof you can't fit in one shot."
  , ""
  , "Your reply must be EXACTLY this format (each marker on its own line):"
  , ""
  , "FORALL: <var> : <Type>, <var> : <Type>, ..."
  , "LHS: <SLL expression using only forall vars>"
  , "RHS: <SLL expression using only forall vars (or fewer)>"
  , "PROOF:"
  , "<Lean 4 proof body, starting with `by`. No markdown fences.>"
  , ""
  , "Use core Lean 4 tactics. Common moves:"
  , "  - `induction <var> with | <Ctr> => ... | ...`"
  , "  - `rfl` for definitional equalities"
  , "  - `simp_all` (no defs list — relies on default simp set)"
  , "  - `show <goal>; rw [ih]` for inductive cases"
  , "  - `rw [<lemma_name>]` or `simp [<lemma_name>]` to use any"
  , "    previously-verified lemma listed above"
  , "  - `Type'.Ctr` to disambiguate constructors (e.g. `Nat'.S`)"
  , ""
  , "If no useful lemma exists for this expression, reply with the"
  , "single word NONE on a line by itself."
  ]
  where
    contextSection
      | null context = []
      | otherwise =
          "Previously-verified lemmas (available as rewrite rules in your proof):"
            : [ "  " ++ lemmaName l ++ ": "
                  ++ showSLL (lemmaLhs l) ++ " = " ++ showSLL (lemmaRhs l)
                  ++ forallSummary l
              | l <- context
              ]
            ++ [""]
    forallSummary l = case lemmaForall l of
      []  -> ""
      fas -> "  (forall "
               ++ commaJoin [n ++ " : " ++ tn | (n, TyCon tn) <- fas]
               ++ ")"

showSLLProgramFull :: Program -> String
showSLLProgramFull (Program fs gs) =
  let ls  = map showFDef fs ++ map showGDef gs
      showFDef (FDef n args body) =
        n ++ "(" ++ commaJoin args ++ ") = " ++ showSLL body ++ ";"
      showGDef (GDef n (Pat cn cvs) args body) =
        n ++ "(" ++ cn ++ "(" ++ commaJoin cvs ++ ")"
          ++ concatMap (", " ++) args
          ++ ") = " ++ showSLL body ++ ";"
  in unlines ls

showTypeDefs :: [DataDef] -> String
showTypeDefs = unlines . map go
  where
    go (DataDef tn ctrs) =
      "  " ++ tn ++ " = " ++
      commaJoin' " | " [showCtr c | c <- ctrs]
    showCtr (CtrDef cn fs) =
      cn ++ "(" ++ commaJoin' ", " (map showTy fs) ++ ")"
    showTy (TyCon n) = n

showFunSigs :: [(Name, ([Type], Type))] -> String
showFunSigs = unlines . map go
  where
    go (n, (args, r)) =
      "  " ++ n ++ " : " ++
      commaJoin' " -> " (map showTy args ++ [showTy r])
    showTy (TyCon t) = t

commaJoin :: [String] -> String
commaJoin = commaJoin' ", "

commaJoin' :: String -> [String] -> String
commaJoin' _ []     = ""
commaJoin' _ [x]    = x
commaJoin' s (x:xs) = x ++ s ++ commaJoin' s xs

-- =========================================================================
-- Response parsing
-- =========================================================================

-- Parse the LLM's structured response into a Lemma. Tolerates leading
-- whitespace and (fenced) markdown wrapping.
parseLemmaResponse :: String -> Name -> Maybe Lemma
parseLemmaResponse raw name = do
  let cleaned = dropWhile isSpace raw
  if "NONE" `isPrefixOf` cleaned then Nothing else do
    forallStr <- extractField "FORALL:" cleaned
    lhsStr    <- extractField "LHS:"    cleaned
    rhsStr    <- extractField "RHS:"    cleaned
    proofStr  <- extractProof          cleaned
    fa        <- parseForalls forallStr
    lhs       <- safeRead lhsStr
    rhs       <- safeRead rhsStr
    return $ Lemma name fa lhs rhs (trim proofStr)

extractField :: String -> String -> Maybe String
extractField key s =
  case dropWhile (not . (key `isPrefixOf`)) (lines s) of
    []     -> Nothing
    (l:_)  -> Just (trim (drop (length key) l))

-- The proof spans from the line "PROOF:" to either an "END" sentinel or
-- end-of-string. Strip any markdown fences along the way.
extractProof :: String -> Maybe String
extractProof s =
  case dropWhile (not . ("PROOF:" `isPrefixOf`)) (lines s) of
    []      -> Nothing
    (_:rest) -> Just $ unlines $ stripFences $ takeWhile (not . isEnd) rest
  where
    isEnd l       = "END" `isPrefixOf` l
    stripFences   = filter (not . isFence)
    isFence l     = "```" `isPrefixOf` (trim l)

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- "n : Nat, m : Bool" → [("n", TyCon "Nat"), ("m", TyCon "Bool")]
parseForalls :: String -> Maybe [(Name, Type)]
parseForalls s = traverse parseOne (splitOn ',' s)
  where
    parseOne piece = case break (== ':') (trim piece) of
      (n, ':':rest) -> Just (trim n, TyCon (trim rest))
      _             -> Nothing

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, [])     -> [a]
  (a, _:rest) -> a : splitOn c rest

safeRead :: Read a => String -> Maybe a
safeRead s = case reads s of
  [(x, r)] | all isSpace r -> Just x
  _                        -> Nothing

-- =========================================================================
-- Bedrock call + verification
-- =========================================================================

-- Ask the LLM for one candidate lemma. Increments the supplied call
-- counter (for stats); doesn't enforce a budget — distillTask's loop
-- bounds the number of attempts. The `context` is the list of
-- previously-verified lemmas, surfaced in the prompt as available
-- rewrite rules so the LLM can decompose hard proofs into chains.
proposeLemma
  :: IORef Int           -- LLM call counter (for stats / accounting)
  -> TypeEnv
  -> Program
  -> [Lemma]             -- previously-verified lemmas
  -> Expr
  -> Name                -- name to assign to the proposed lemma
  -> IO (Maybe Lemma)
proposeLemma counter env prog context e name = do
  modifyIORef' counter (+1)
  k <- readIORef counter
  hPutStrLn stderr $ "  [distill] requesting lemma #" ++ show k
                       ++ " for: " ++ showSLL e
  result <- try (chat (buildLemmaPrompt env prog context e))
              :: IO (Either SomeException String)
  case result of
    Left err -> do
      hPutStrLn stderr $ "  [distill] LLM error: " ++ show err
      return Nothing
    Right resp -> do
      hPutStrLn stderr $ "  [distill] response: " ++ take 200 resp
      case parseLemmaResponse resp name of
        Nothing -> do
          hPutStrLn stderr "  [distill] parse failed (or NONE)"
          return Nothing
        Just lem -> do
          hPutStrLn stderr $ "  [distill] parsed: "
            ++ showSLL (lemmaLhs lem) ++ " = " ++ showSLL (lemmaRhs lem)
          return (Just lem)

-- Verify a candidate lemma. The Conjecture file inlines all
-- previously-verified lemmas so the new proof can reference them.
-- On verification failure, ask the LLM to fix the proof — up to
-- `retries` attempts. Each retry is one Bedrock call charged to the
-- shared counter. The LHS/RHS/forall stay fixed; only the proof body
-- changes.
verifyLemma
  :: IORef Int           -- LLM call counter
  -> Int                 -- proof-retry budget (0 = no retry)
  -> TypeEnv
  -> Program
  -> [Lemma]
  -> Lemma
  -> LeanProject
  -> IO (Maybe Lemma)    -- Just the verified lemma (with possibly
                         --   updated proof), or Nothing if all
                         --   attempts failed
verifyLemma counter retries env prog context lem proj = go 0 lem
  where
    go n l = do
      v <- verify proj (embedLemma env prog context l)
      case v of
        Ok -> do
          hPutStrLn stderr "  [distill] lemma verified by Lean"
          return (Just l)
        Failed s
          | n >= retries -> do
              hPutStrLn stderr $ "  [distill] lemma rejected: " ++ take 200 s
              return Nothing
          | otherwise -> do
              hPutStrLn stderr $ "  [distill] proof failed (attempt "
                ++ show (n+1) ++ "/" ++ show (retries+1) ++ "), retrying"
              mLem' <- retryProof counter env prog context l s
              case mLem' of
                Nothing -> do
                  hPutStrLn stderr "  [distill] retry produced no proof; giving up"
                  return Nothing
                Just l' -> go (n + 1) l'

-- Ask the LLM to fix the proof of an existing lemma, given Lean's
-- failure output. Reuses the lemma's forall/lhs/rhs verbatim; the
-- response is just a new `by …` block.
retryProof
  :: IORef Int
  -> TypeEnv
  -> Program
  -> [Lemma]
  -> Lemma               -- the lemma whose proof needs fixing
  -> String              -- Lean's stdout/stderr from the failed verify
  -> IO (Maybe Lemma)
retryProof counter env prog context lem err = do
  modifyIORef' counter (+1)
  k <- readIORef counter
  hPutStrLn stderr $ "  [distill] retry-proof call #" ++ show k
  let prompt = buildRetryPrompt env prog context lem err
  result <- try (chat prompt) :: IO (Either SomeException String)
  case result of
    Left e -> do
      hPutStrLn stderr $ "  [distill] LLM error during retry: " ++ show e
      return Nothing
    Right resp -> do
      let body = extractProofBody resp
      hPutStrLn stderr $ "  [distill] retry body: " ++ take 200 body
      if null body
        then return Nothing
        else return (Just lem { lemmaProof = body })

-- Walk the LLM response and pull out the first `by …` block. Tolerates
-- preamble and markdown fences. Mirrors LLMSupercompiler.extractProofBody
-- (kept local here to avoid an import cycle).
extractProofBody :: String -> String
extractProofBody resp =
  stopAtFence (dropToBy (stripFences (trim resp)))
  where
    stripFences s = unlines [l | l <- lines s, not (isFence (trim l))]
    isFence l = "```" `isPrefixOf` l
    dropToBy s
      | "by " `isPrefixOf` s  = s
      | "by\n" `isPrefixOf` s = s
      | null s = s
      | otherwise = dropToBy (drop 1 s)
    stopAtFence ('`':'`':'`':_) = ""
    stopAtFence (c:r) = c : stopAtFence r
    stopAtFence [] = []

buildRetryPrompt :: TypeEnv -> Program -> [Lemma] -> Lemma -> String -> String
buildRetryPrompt env prog context lem err = unlines $
  [ "You proposed a Lean lemma but the proof failed to verify."
  , "Please fix the proof. Keep the lemma statement (forall/lhs/rhs)"
  , "exactly the same; only the `by …` proof body changes."
  , ""
  , "Type declarations:"
  , showTypeDefs (typeDefs env)
  , ""
  , "Function signatures:"
  , showFunSigs (funSigs env)
  , ""
  , "Program (for reference):"
  , showSLLProgramFull prog
  , ""
  ] ++ contextSection ++
  [ "Lemma to prove:"
  , "  forall " ++ forallStr ++ ", "
      ++ showSLL (lemmaLhs lem) ++ " = " ++ showSLL (lemmaRhs lem)
  , ""
  , "Your previous proof attempt:"
  , trim (lemmaProof lem)
  , ""
  , "Lean's error:"
  , take 1500 err
  , ""
  , "Common fixes:"
  , "  - `simp` (without `only`) reduces more aggressively than"
  , "    `simp only [...]` and often closes goals where `exact ih`"
  , "    or `rfl` would otherwise fail by a constructor."
  , "  - Use `Nat'.S` (or `LSym'.Cons` etc.) when matching on"
  , "    constructors in `show` or `case` clauses; bare `S` won't"
  , "    resolve in our embedding."
  , "  - In inductive cases, `simp_all` is often enough; try it"
  , "    before reaching for `exact ih`."
  , "  - `rw [<lemma_name>]` to apply a previously-verified lemma."
  , ""
  , "Reply with ONLY the proof body — a single Lean 4 expression"
  , "starting with `by `. No markdown fences, no explanation."
  ]
  where
    forallStr = commaJoin
      [ n ++ " : " ++ tn | (n, TyCon tn) <- lemmaForall lem ]
    contextSection
      | null context = []
      | otherwise =
          "Previously-verified lemmas (available as rewrite rules):"
            : [ "  " ++ lemmaName l ++ ": "
                  ++ showSLL (lemmaLhs l) ++ " = " ++ showSLL (lemmaRhs l)
              | l <- context
              ]
            ++ [""]

-- =========================================================================
-- The pre-pass
-- =========================================================================

-- Iteratively propose / verify / rewrite, up to `budget` proposals.
-- Verified lemmas accumulate in a context list that is shown to the
-- LLM in subsequent prompts (so proofs can chain) and inlined into
-- subsequent Conjecture files (so Lean recognizes them as rewrite
-- rules). We keep verified lemmas in the chain even when their LHS
-- doesn't pattern-match the current expression — they may help prove
-- a later lemma.
distillTask
  :: IORef Int           -- LLM call counter (for stats)
  -> Int                 -- per-distillation budget (max proposals)
  -> Int                 -- proof-retry budget per lemma
  -> TypeEnv
  -> Program
  -> LeanProject
  -> Expr                -- input expression
  -> IO Expr             -- distilled expression (may equal input)
distillTask counter budget proofRetries env prog proj = go 1 []
  where
    go i ctx e | i > budget = return e
    go i ctx e = do
      let lemName = "lemma_" ++ show i
      mLem <- proposeLemma counter env prog ctx e lemName
      case mLem of
        Nothing  -> return e        -- LLM declined or parse failed; stop
        Just lem -> do
          mVerified <- verifyLemma counter proofRetries env prog ctx lem proj
          case mVerified of
            Nothing   -> go (i + 1) ctx e
            Just lem' ->
              -- verified — accumulate in context regardless of whether
              -- it rewrites the current expression
              let ctx' = ctx ++ [lem']
              in case rewriteWith lem' e of
                   Nothing -> do
                     hPutStrLn stderr
                       "  [distill] lemma verified, kept in context (no match for e)"
                     go (i + 1) ctx' e
                   Just e' -> do
                     hPutStrLn stderr $ "  [distill] applied: " ++ showSLL e'
                     go (i + 1) ctx' e'

