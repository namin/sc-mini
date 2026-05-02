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
import System.IO
import Text.Printf (printf)

data PerfBench = PerfBench
  { pbName  :: String
  , pbTask  :: Task
  , pbTypes :: TypeEnv
  , pbCases :: [(String, Subst)]
  }

-- KMP test inputs are lists of A/B symbols.
data Sym = A | B
  deriving Show

lsym :: [Sym] -> Expr
lsym []     = Ctr "Nil" []
lsym (s:ss) = Ctr "Cons" [Ctr (show s) [], lsym ss]

-- Test cases per benchmark. Inputs scale up so we can see whether the
-- residual gets faster as the input grows (a constant-factor speedup
-- shows up everywhere; an asymptotic speedup widens with input size).
benchmarks :: [PerfBench]
benchmarks =
  [ PerfBench
      "even-square"
      ([expr|gEven(fSqr(x))|], prog1)
      prog1Types
      [(show k, [("x", peano k)]) | k <- [0, 2, 4, 6, 8, 10, 12]]
  , PerfBench
      "add-assoc"
      ([expr|gAdd(gAdd(x, y), z)|], prog1)
      prog1Types
      [ (show k, [("x", peano k), ("y", peano k), ("z", peano k)])
      | k <- [0, 1, 2, 4, 6, 8, 10]
      ]
  , PerfBench
      "half-of-double"
      ([expr|gEq(gHalf(gDouble(n)), n)|], prog3)
      prog3Types
      [(show k, [("n", peano k)]) | k <- [0, 2, 4, 6, 8, 10, 12]]
  , PerfBench
      "kmp-aa"
      ([expr|fMatch(Cons(A(), Cons(A(), Nil())), s)|], prog2)
      prog2Types
      [ ("AA",          [("s", lsym [A, A])])
      , ("BAA",         [("s", lsym [B, A, A])])
      , ("BABA",        [("s", lsym [B, A, B, A])])
      , ("BBAA",        [("s", lsym [B, B, A, A])])
      , ("ABABAA",      [("s", lsym [A, B, A, B, A, A])])
      , ("BBBBAA",      [("s", lsym [B, B, B, B, A, A])])
      ]
  ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "Performance comparison: original vs classical vs LLM-supercompiled."
  putStrLn "(This makes real Bedrock calls for the LLM residuals.)"
  putStrLn ""
  mapM_ runPerf benchmarks
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
