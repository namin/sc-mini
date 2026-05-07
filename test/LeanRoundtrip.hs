-- End-to-end smoke test: embedProgram produces Lean source that
-- `lake build` accepts under the toolchain pinned in LeanCheck, and
-- a trivial conjecture verifies. No LLM in the loop.
--
-- Exits 0 on success, non-zero on failure (exitcode-stdio-1.0).

module Main where

import Control.Exception (bracket)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)

import Demonstration (prog1, prog1Types)
import LeanCheck (Verdict(..), setupProject, teardownProject, verify)

main :: IO ()
main = bracket (setupProject prog1Types prog1) teardownProject $ \proj -> do
  let conjecture = unlines
        [ "import Program"
        , "theorem trivial_ok : True := True.intro"
        ]
  v <- verify proj conjecture
  case v of
    Ok       -> exitSuccess
    Failed o -> do
      hPutStrLn stderr "lean-roundtrip: trivial verify failed"
      hPutStrLn stderr o
      exitFailure
