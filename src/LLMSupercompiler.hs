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
import Data.Maybe (fromMaybe)
import Data.IORef
import Control.Exception (try, SomeException)
import System.IO (hFlush, stdout, hPutStrLn, stderr)

maxLLMCalls :: Int
maxLLMCalls = 20

maxDepth :: Int
maxDepth = 1000

supercompileIO :: Task -> IO Task
supercompileIO (e, p) = do
  counter <- newIORef (0 :: Int)
  tree <- buildFTreeIO counter (addPropagation $ driveMachine p) p e
  return $ residuate $ simplify $ foldTree tree

supercompilePure :: Task -> Task
supercompilePure (e, p) =
  residuate $ simplify $ foldTree $ buildFTreePure (addPropagation $ driveMachine p) e

buildFTreeIO :: IORef Int -> Machine Conf -> Program -> Conf -> IO (Tree Conf)
buildFTreeIO counter m p e = bftIO counter m p nameSupply 0 e

buildFTreePure :: Machine Conf -> Conf -> Tree Conf
buildFTreePure m e = bftPure m nameSupply e

bftPure :: Machine Conf -> NameSupply -> Conf -> Tree Conf
bftPure d (n:ns) e | whistle e = bftPure d ns $ classicalGeneralize n e
bftPure d ns     t = case d ns t of
  Decompose ds -> Node t $ Decompose $ map (bftPure d ns) ds
  Transient e  -> Node t $ Transient $ bftPure d ns e
  Stop         -> Node t Stop
  Variants cs  -> Node t $ Variants [(c, bftPure d (unused c ns) e) | (c, e) <- cs]

bftIO :: IORef Int -> Machine Conf -> Program -> NameSupply -> Int -> Conf -> IO (Tree Conf)
bftIO counter d p (n:ns) depth e | whistle e = do
  calls <- readIORef counter
  if calls >= maxLLMCalls || depth >= maxDepth
    then do
      hPutStrLn stderr $ "  [whistle] budget exhausted, classical generalization"
      bftIO counter d p ns depth (classicalGeneralize n e)
    else do
      hPutStrLn stderr $ "  [whistle] " ++ showSLL e
      gen <- llmGeneralize counter p n e
      bftIO counter d p ns depth gen
bftIO counter d p ns depth t
  | depth >= maxDepth = return $ Node t Stop
  | otherwise = case d ns t of
      Decompose ds -> do
        cs <- mapM (bftIO counter d p ns (depth+1)) ds
        return $ Node t $ Decompose cs
      Transient e -> do
        c <- bftIO counter d p ns (depth+1) e
        return $ Node t $ Transient c
      Stop -> return $ Node t Stop
      Variants cs -> do
        cs' <- sequence [(,) c <$> bftIO counter d p (unused c ns) (depth+1) e | (c, e) <- cs]
        return $ Node t $ Variants cs'

sizeBound :: Integer
sizeBound = 15

whistle :: Expr -> Bool
whistle e@(FCall _ args) = not (all isVar args) && size e > sizeBound
whistle e@(GCall _ args) = not (all isVar args) && size e > sizeBound
whistle _ = False

llmGeneralize :: IORef Int -> Program -> Name -> Conf -> IO Conf
llmGeneralize counter prog freshName expr = do
  modifyIORef' counter (+1)
  calls <- readIORef counter
  let prompt = buildPrompt prog expr freshName
  hPutStrLn stderr $ "  [llm] call #" ++ show calls ++ ", asking for generalization..."
  result <- try (chat prompt) :: IO (Either SomeException String)
  case result of
    Left err -> do
      hPutStrLn stderr $ "  [llm] error: " ++ show err
      hPutStrLn stderr "  [llm] falling back to classical"
      return $ classicalGeneralize freshName expr
    Right response -> do
      hPutStrLn stderr $ "  [llm] response: " ++ take 200 response
      case tryParse response of
        Just parsed -> do
          hPutStrLn stderr $ "  [llm] parsed OK: " ++ showSLL parsed
          return parsed
        Nothing -> do
          hPutStrLn stderr "  [llm] could not parse, falling back to classical"
          return $ classicalGeneralize freshName expr

buildPrompt :: Program -> Conf -> Name -> String
buildPrompt prog expr freshName =
  unlines
    [ "You are a supercompiler assistant. You help generalize expressions in SLL"
    , "(Simple Lazy Language) to ensure termination while preserving semantics."
    , ""
    , "SLL syntax (you MUST use this exact syntax in your reply):"
    , "  Variables: x, y, v1, v2, ..."
    , "  Constructors: Name(arg1, arg2, ...) e.g. S(x), Z(), Cons(x, xs), Nil()"
    , "  F-calls: fName(arg1, ...) — names start with 'f', e.g. fSqr(x)"
    , "  G-calls: gName(arg1, ...) — names start with 'g', e.g. gAdd(x, y)"
    , "  Let: let v = e1 in e2"
    , ""
    , "IMPORTANT: Function names MUST keep their g/f prefix: gAdd, gMult, fSqr, etc."
    , ""
    , "The program definitions are:"
    , showSLLProgram prog
    , ""
    , "During supercompilation, the following expression has grown too large"
    , "and we need to GENERALIZE it to ensure termination."
    , ""
    , "Expression to generalize:"
    , "  " ++ showSLL expr
    , ""
    , "To generalize, extract a subexpression into a let-binding using the"
    , "fresh variable '" ++ freshName ++ "'. The result must be:"
    , "  let " ++ freshName ++ " = <subexpr> in <body-with-" ++ freshName ++ ">"
    , ""
    , "Choose the subexpression that is MOST LIKELY causing the term to grow —"
    , "typically the largest non-variable argument, or a recursive call that"
    , "will enable folding (detecting a loop) in subsequent driving steps."
    , ""
    , "Think about what transformation would help the supercompiler find a"
    , "finite representation. Consider:"
    , "  - Which subexpression is growing unboundedly?"
    , "  - Would extracting it allow the residual to fold back to an ancestor?"
    , "  - Is there an accumulator pattern that could be introduced?"
    , ""
    , "Reply with ONLY the generalized expression on a single line."
    , "No explanation, no markdown, just the SLL expression."
    , "Example: let v5 = gAdd(x, y) in gMult(v5, v5)"
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
safeParse s = case [(e, r) | (e, r) <- reads s, all isSpace r] of
  (expr, _):_ -> Just expr
  _           -> Nothing

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs

strip :: String -> String
strip = reverse . dropWhile (== '\n') . reverse . dropWhile (== '\n')

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
