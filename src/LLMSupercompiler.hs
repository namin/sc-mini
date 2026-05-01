{-# LANGUAGE OverloadedStrings #-}

module LLMSupercompiler (supercompileIO, supercompilePure) where

import Data
import DataUtil
import DataIO
import Driving
import Folding
import Generator
import Deforester (simplify)
import Supercompiler (addPropagation)
import Bedrock

import Data.List (intercalate)
import Data.IORef
import Control.Exception (try, SomeException)
import System.IO (hPutStrLn, stderr)

maxLLMCalls :: Int
maxLLMCalls = 10

supercompileIO :: Task -> IO Task
supercompileIO (e, p) = do
  counter <- newIORef (0 :: Int)
  tree <- bftIO counter (addPropagation $ driveMachine p) p nameSupply [] e
  return $ residuate $ simplify $ foldTree tree

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

-- IO version with LLM generalization
bftIO :: IORef Int -> Machine Conf -> Program -> NameSupply -> [Conf] -> Conf -> IO (Tree Conf)
bftIO counter d p (n:ns) hist e
  | whistleCandidate e, Just anc <- findEmbedding hist e = do
      calls <- readIORef counter
      if calls >= maxLLMCalls
        then do
          let hist' = filter (/= anc) hist
          hPutStrLn stderr "  [whistle] budget exhausted, using msg"
          bftIO counter d p ns hist' (msgToLet (n:ns) e anc)
        else do
          let hist' = filter (/= anc) hist
          hPutStrLn stderr $ "  [whistle] HE detected"
          hPutStrLn stderr $ "    ancestor:  " ++ showSLL anc
          hPutStrLn stderr $ "    current:   " ++ showSLL e
          gen <- llmGeneralize counter p anc n e ns
          bftIO counter d p ns hist' gen
bftIO counter d p ns hist t = case d ns t of
  Decompose ds -> do
    cs <- mapM (bftIO counter d p ns hist') ds
    return $ Node t $ Decompose cs
  Transient e -> do
    c <- bftIO counter d p ns hist' e
    return $ Node t $ Transient c
  Stop -> return $ Node t Stop
  Variants cs -> do
    cs' <- sequence [(,) c <$> bftIO counter d p (unused c ns) hist' e | (c, e) <- cs]
    return $ Node t $ Variants cs'
  where hist' = if isCall t then t : hist else hist

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

-- Ask the LLM to generalize given the ancestor/descendant pair
llmGeneralize :: IORef Int -> Program -> Conf -> Name -> Conf -> NameSupply -> IO Conf
llmGeneralize counter prog ancestor freshName expr ns = do
  modifyIORef' counter (+1)
  calls <- readIORef counter
  let prompt = buildPrompt prog ancestor expr freshName
      fallback = msgToLet ns expr ancestor
  hPutStrLn stderr $ "  [llm] call #" ++ show calls
  result <- try (chat prompt) :: IO (Either SomeException String)
  case result of
    Left err -> do
      hPutStrLn stderr $ "  [llm] error: " ++ show err ++ ", falling back to msg"
      return fallback
    Right response -> do
      hPutStrLn stderr $ "  [llm] response: " ++ take 200 response
      case tryParse response of
        Just parsed -> do
          hPutStrLn stderr $ "  [llm] parsed: " ++ showSLL parsed
          return parsed
        Nothing -> do
          hPutStrLn stderr "  [llm] parse failed, falling back to msg"
          return fallback

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
