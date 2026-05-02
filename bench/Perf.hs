{-# LANGUAGE QuasiQuotes #-}

-- Performance comparison harness.
--
-- For each benchmark, we get three programs:
--   1. The original (untransformed input task)
--   2. The classical supercompiled residual (sc-mini's `supercompile`)
--   3. The LLM-supercompiled residual (`supercompileIOWithTypes`)
--
-- Then we run each on a series of concrete test inputs via `intC` (the
-- counting interpreter from Interpreter.hs) and report:
--   * step counts per input for each variant
--   * value agreement across all three (correctness sanity-check)
--   * speedup ratios (classical/orig, llm/orig, llm/classical)
--
-- The whole point: function count is a proxy for residual *size*,
-- not residual *runtime*. This harness measures runtime directly.
--
-- Run with:  stack exec llm-perf
-- (Like llm-bench, makes real Bedrock calls during the LLM
-- supercompiles; ~12 calls total across the four benchmarks.)

module Main where

import Data
import DataIO
import Demonstration
import Interpreter (sll_trace)
import LLMSupercompiler (supercompileIOWithTypes)
import Supercompiler (supercompile)
import Types

import Data.List (intercalate)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO
import Text.Printf (printf)

data PerfBench = PerfBench
  { pbName    :: String
  , pbTask    :: Task
  , pbTypes   :: TypeEnv
  , pbCases   :: [(String, Subst)]
  , pbDefault :: Bool   -- include in default (no-args) run?
  }

-- KMP test inputs are lists of A/B symbols.
data Sym = A | B
  deriving Show

lsym :: [Sym] -> Expr
lsym []     = Ctr "Nil" []
lsym (s:ss) = Ctr "Cons" [Ctr (show s) [], lsym ss]

-- Lists of Nat for prog5.
nat :: Int -> Expr
nat 0 = Ctr "Z" []
nat n = Ctr "S" [nat (n - 1)]

lnat :: [Int] -> Expr
lnat []     = Ctr "Nil" []
lnat (x:xs) = Ctr "Cons" [nat x, lnat xs]

-- Aexp constructors for prog6.
aNum :: Int -> Expr
aNum n = Ctr "ANum" [nat n]

aAdd :: Expr -> Expr -> Expr
aAdd e1 e2 = Ctr "AAdd" [e1, e2]

-- Test cases per benchmark. Inputs scale up so we can see whether the
-- residual gets faster as the input grows (a constant-factor speedup
-- shows up everywhere; an asymptotic speedup widens with input size).
benchmarks :: [PerfBench]
benchmarks =
  [ PerfBench "even-square"
      ([expr|gEven(fSqr(x))|], prog1) prog1Types
      [(show k, [("x", peano k)]) | k <- [0, 2, 4, 6, 8, 10, 12]]
      True
  , PerfBench "add-assoc"
      ([expr|gAdd(gAdd(x, y), z)|], prog1) prog1Types
      [ (show k, [("x", peano k), ("y", peano k), ("z", peano k)])
      | k <- [0, 1, 2, 4, 6, 8, 10]
      ]
      True
  , PerfBench "half-of-double"
      ([expr|gEq(gHalf(gDouble(n)), n)|], prog3) prog3Types
      [(show k, [("n", peano k)]) | k <- [0, 2, 4, 6, 8, 10, 12]]
      True
  , PerfBench "kmp-aa"
      ([expr|fMatch(Cons(A(), Cons(A(), Nil())), s)|], prog2) prog2Types
      [ ("AA",          [("s", lsym [A, A])])
      , ("BAA",         [("s", lsym [B, A, A])])
      , ("BABA",        [("s", lsym [B, A, B, A])])
      , ("BBAA",        [("s", lsym [B, B, A, A])])
      , ("ABABAA",      [("s", lsym [A, B, A, B, A, A])])
      , ("BBBBAA",      [("s", lsym [B, B, B, B, A, A])])
      ]
      True
  , PerfBench "add-commute"
      ([expr|gEq(gAdd(x, y), gAdd(y, x))|], prog3) prog3Types
      [ (show k ++ "/" ++ show (k+1),
         [("x", peano k), ("y", peano (k+1))])
      | k <- [0, 1, 2, 4, 6, 8, 10]
      ]
      True
  , PerfBench "reverse-involution"
      ([expr|gReverse(gReverse(xs))|], prog5) prog5Types
      [ ("len" ++ show n, [("xs", lnat (take n [0..]))])
      | n <- [0, 1, 2, 3, 5, 7, 10]
      ]
      True
  , PerfBench "length-distributes"
      ([expr|gLength(gAppend(xs, ys))|], prog5) prog5Types
      [ (show m ++ "+" ++ show n,
         [("xs", lnat (take m [0..])), ("ys", lnat (take n [0..]))])
      | (m, n) <- [(0,0), (1,1), (2,3), (3,2), (5,5), (7,3), (10,10)]
      ]
      True
  -- eval-fold: tier 2 interpreter benchmark. Slow and tends to
  -- distill-fail; opt-in only via explicit name argument.
  , PerfBench "eval-fold"
      ([expr|gEval(gFold(e))|], prog6) prog6Types
      [ ("3+5",    [("e", aAdd (aNum 3) (aNum 5))])
      , ("(2+3)+4", [("e", aAdd (aAdd (aNum 2) (aNum 3)) (aNum 4))])
      , ("2+(3+4)", [("e", aAdd (aNum 2) (aAdd (aNum 3) (aNum 4)))])
      , ("nested", [("e", aAdd (aAdd (aNum 1) (aNum 2))
                                (aAdd (aNum 3) (aNum 4)))])
      ]
      False
  ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  let selected = case args of
        []    -> filter pbDefault benchmarks
        names -> filter (\b -> pbName b `elem` names) benchmarks
  case (args, selected) of
    (a:_, []) -> do
      putStrLn $ "No benchmark matches: " ++ show a
      putStrLn $ "Available: " ++ unwords (map pbName benchmarks)
      exitFailure
    _ -> return ()
  putStrLn "Performance comparison: original vs classical vs LLM-supercompiled."
  putStrLn "(This makes real Bedrock calls for the LLM residuals.)"
  putStrLn ""
  mapM_ runPerf selected
  putStrLn ""
  putStrLn "Lower step counts are faster. Ratios <1.0 mean speedup, >1.0 mean slowdown."

runPerf :: PerfBench -> IO ()
runPerf pb = do
  putStrLn $ "==> " ++ pbName pb
  hFlush stdout
  let task     = pbTask pb
      classic  = supercompile task
  llm <- supercompileIOWithTypes (pbTypes pb) task
  let sizeOf (_, Program fs gs) = length fs + length gs
  printf "    sizes: orig=%d  classical=%d  llm=%d\n"
         (sizeOf task) (sizeOf classic) (sizeOf llm)
  putStrLn "    input    |  orig  |  class |   llm  | cls/orig |  llm/orig | llm/cls"
  putStrLn "    ---------+--------+--------+--------+----------+-----------+--------"
  mapM_ (runCase task classic llm) (pbCases pb)
  putStrLn ""

runCase :: Task -> Task -> Task -> (String, Subst) -> IO ()
runCase orig clas llm (label, env) = do
  let (vO, nO) = sll_trace orig env
      (vC, nC) = sll_trace clas env
      (vL, nL) = sll_trace llm env
      same     = vO == vC && vC == vL
      ratio :: Integer -> Integer -> Double
      ratio a b = if b == 0 then 0/0 else fromIntegral a / fromIntegral b
      flag     = if same then "" else "  *** VALUE MISMATCH (orig/cls/llm differ) ***"
  printf "    %-8s |  %5d |  %5d |  %5d |   %5.2f  |   %5.2f   |  %5.2f%s\n"
         label nO nC nL
         (ratio nC nO) (ratio nL nO) (ratio nL nC)
         flag
