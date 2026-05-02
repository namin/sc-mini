{-# LANGUAGE QuasiQuotes #-}

-- LLM-supercompiler benchmark harness.
--
-- Runs each benchmark via `supercompileIOWithTypes`, capturing the
-- supercompiler's stderr trace into a per-benchmark file. After each
-- run we parse the trace for event counts (whistles, LLM calls,
-- auto-prove verdicts, fold back-edges) and emit a summary line.
--
-- The benchmark `passes` if the supercompile terminates and the residual
-- function count falls inside an expected range. We deliberately do not
-- pin the count exactly: the LLM is non-deterministic, so different runs
-- may produce slightly different residuals.
--
-- Run with:  stack run llm-bench
-- (Requires AWS credentials at ~/.aws/credentials and a working `lake`
-- via ~/.elan/bin/lake. Each run makes real Bedrock calls.)

module Main where

import Data
import DataIO
import Demonstration
import LLMSupercompiler
import Types

import Control.Exception (try, SomeException)
import Data.List (isInfixOf)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.IO

data Benchmark = Benchmark
  { benchName     :: String
  , benchTask     :: Task
  , benchTypes    :: TypeEnv
  , benchExpected :: (Int, Int)  -- inclusive range for residual function count
  }

benchmarks :: [Benchmark]
benchmarks =
  [ Benchmark
      "even-square"
      ([expr|gEven(fSqr(x))|], prog1)
      prog1Types
      (5, 30)
  , Benchmark
      "add-assoc"
      ([expr|gAdd(gAdd(x, y), z)|], prog1)
      prog1Types
      (5, 25)
  , Benchmark
      "half-of-double"
      ([expr|gEq(gHalf(gDouble(n)), n)|], prog3)
      prog3Types
      (5, 30)
  , Benchmark
      "kmp-aa"
      ([expr|fMatch(Cons(A(), Cons(A(), Nil())), s)|], prog2)
      prog2Types
      (5, 40)
  ]

data Stats = Stats
  { sFolds    :: !Int
  , sWhistles :: !Int
  , sLLMCalls :: !Int
  , sAutoOk   :: !Int
  , sAutoFail :: !Int
  , sLLMProof :: !Int
  , sBudget   :: !Int
  , sMaxHit   :: !Bool
  }

parseStats :: String -> Stats
parseStats trace = Stats
  { sFolds    = cnt "[fold] back"
  , sWhistles = cnt "[whistle] HE"
  , sLLMCalls = cnt "[llm] call"
  , sAutoOk   = cnt "auto-prove Ok"
  , sAutoFail = cnt "auto-prove Failed"
  , sLLMProof = cnt "[llm-proof] call"
  , sBudget   = cnt "budget exhausted"
  , sMaxHit   = any ("exceeded maxWhistles" `isInfixOf`) ls
  }
  where
    ls = lines trace
    cnt sub = length (filter (sub `isInfixOf`) ls)

-- Capture stderr emitted while the action runs into a file; return the
-- file's contents alongside the action's result. Uses hDuplicateTo to
-- swap the stderr file descriptor in-place, so any stderr write inside
-- the action goes to the file regardless of how it gets there.
captureTrace :: FilePath -> IO a -> IO (a, String)
captureTrace path action = do
  result <- withFile path WriteMode $ \h -> do
    hSetBuffering h LineBuffering
    oldErr <- hDuplicate stderr
    hDuplicateTo h stderr
    a <- action
    hFlush stderr
    hDuplicateTo oldErr stderr
    hClose oldErr
    return a
  trace <- readFile path
  return (result, trace)

runBench :: FilePath -> Benchmark -> IO Bool
runBench traceDir b = do
  hPutStrLn stdout $ "==> " ++ benchName b
  hFlush stdout
  let tracePath = traceDir ++ "/" ++ benchName b ++ ".trace"
  outcome <-
    try (captureTrace tracePath
           (supercompileIOWithTypes (benchTypes b) (benchTask b)))
      :: IO (Either SomeException (Task, String))
  case outcome of
    Left ex -> do
      putStrLn $ "    FAILED: " ++ take 200 (show ex)
      putStrLn $ "    trace at " ++ tracePath
      return False
    Right ((residual, Program fs gs), trace) -> do
      let nFns     = length fs + length gs
          (lo, hi) = benchExpected b
          countOk  = nFns >= lo && nFns <= hi
          stats    = parseStats trace
          -- Pass criterion: supercompile terminated, residual size in
          -- the expected range, max-whistles cap not hit. Auto-prove
          -- failures are not failure-mode — the supercompiler falls
          -- back to classical generalization (correct by construction)
          -- when Lean rejects an LLM proposal, so the residual is
          -- still valid. Lean's verdict counts are reported for
          -- transparency, not as gate.
          ok       = countOk && not (sMaxHit stats)
      putStrLn $ "    residual: " ++ showSLL residual
      putStrLn $ "    functions: " ++ show nFns
                   ++ " (expected " ++ show lo ++ "-" ++ show hi ++ ")"
      putStrLn $ "    whistles: " ++ show (sWhistles stats)
                   ++ "  folds: " ++ show (sFolds stats)
                   ++ "  llm: " ++ show (sLLMCalls stats)
                   ++ "  auto-prove: " ++ show (sAutoOk stats) ++ " ok / "
                                       ++ show (sAutoFail stats) ++ " fail"
                   ++ "  llm-proof: " ++ show (sLLMProof stats)
                   ++ "  budget: " ++ show (sBudget stats)
                   ++ (if sMaxHit stats then "  [HIT MAX-WHISTLES]" else "")
      putStrLn $ "    " ++ if ok then "PASS" else "FAIL"
      putStrLn $ "    trace: " ++ tracePath
      return ok

main :: IO ()
main = do
  let traceDir = "bench/results"
  createDirectoryIfMissing True traceDir
  putStrLn "Running LLM-supercompiler benchmarks (real Bedrock calls)."
  putStrLn $ "Per-benchmark stderr traces under " ++ traceDir ++ "/"
  putStrLn ""
  results <- mapM (runBench traceDir) benchmarks
  let passed = length (filter id results)
      total  = length results
  putStrLn ""
  putStrLn $ "Summary: " ++ show passed ++ "/" ++ show total ++ " passed."
  if passed == total then return () else exitFailure
