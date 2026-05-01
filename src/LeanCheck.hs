{-# LANGUAGE ScopedTypeVariables #-}

module LeanCheck
  ( LeanProject(..)
  , Verdict(..)
  , setupProject
  , verify
  , teardownProject
  ) where

import Data
import Types
import LeanEmbed (embedProgram)

import Control.Exception (catch, SomeException)
import Data.IORef
import System.Directory
import System.Environment (getEnv)
import System.Exit
import System.FilePath
import System.IO.Temp
import System.Process

-- A handle to a per-supercompile-run lake project under a tempdir.
-- Holds the proofs/ path and a counter for unique conjecture filenames.
data LeanProject = LeanProject
  { projDir     :: FilePath   -- absolute path to <runDir>/proofs
  , projCounter :: IORef Int
  }

-- Lean reports diagnostics on *stdout*, not stderr. The `failedOutput`
-- field carries whichever of stdout/stderr was non-empty (concatenated).
data Verdict
  = Ok
  | Failed { failedOutput :: String }
  deriving (Show, Eq)

-- =========================================================================
-- Lake scaffold (fixed per-run, regenerated each setup)
-- =========================================================================

lakefileToml :: String
lakefileToml = unlines
  [ "name = \"scproofs\""
  , "defaultTargets = [\"Program\"]"
  , ""
  , "[[lean_lib]]"
  , "name = \"Program\""
  ]

-- Pinned to match the toolchain noted in DUMP.md. If the user's elan has
-- 4.29.1 already, this avoids any download.
leanToolchain :: String
leanToolchain = "leanprover/lean4:v4.29.1\n"

-- =========================================================================
-- Binary discovery
-- =========================================================================

-- We assume elan is installed at $HOME/.elan (per DUMP.md). The wrappers
-- there honor the project's lean-toolchain file automatically.
elanBin :: String -> IO FilePath
elanBin name = do
  home <- getEnv "HOME"
  return (home </> ".elan" </> "bin" </> name)

-- =========================================================================
-- Setup / teardown
-- =========================================================================

-- Create <tempdir>/sc-mini-XXXX/proofs, write the scaffold + Program.lean,
-- run `lake build`. Returns a handle the verifier can use.
setupProject :: TypeEnv -> Program -> IO LeanProject
setupProject env prog = do
  base   <- getCanonicalTemporaryDirectory
  runDir <- createTempDirectory base "sc-mini-"
  let proofs = runDir </> "proofs"
  createDirectoryIfMissing True proofs
  writeFile (proofs </> "lakefile.toml") lakefileToml
  writeFile (proofs </> "lean-toolchain") leanToolchain
  writeFile (proofs </> "Program.lean") (embedProgram env prog)
  lake <- elanBin "lake"
  (exitCode, out, err) <- readCreateProcessWithExitCode
    (proc lake ["build"]) { cwd = Just proofs } ""
  case exitCode of
    ExitSuccess   -> return ()
    ExitFailure c -> error $ unlines
      [ "LeanCheck.setupProject: lake build failed (exit " ++ show c ++ ")"
      , "  proofs dir: " ++ proofs
      , "  output:"
      , out ++ err
      ]
  ref <- newIORef 0
  return (LeanProject proofs ref)

-- Removes the entire run dir (the parent of proofs/). Caller decides
-- whether to tear down on success or keep the dir for inspection.
teardownProject :: LeanProject -> IO ()
teardownProject proj = do
  let runDir = takeDirectory (projDir proj)
  removeDirectoryRecursive runDir
    `catch` \(_ :: SomeException) -> return ()

-- =========================================================================
-- Verification
-- =========================================================================

-- Write Conjecture_<n>.lean and run `lake env lean` against it.
-- `lake env` sets LEAN_PATH so `import Program` resolves to the .olean
-- built by setupProject.
verify :: LeanProject -> String -> IO Verdict
verify proj conjectureSrc = do
  n <- atomicModifyIORef' (projCounter proj) (\i -> let i' = i + 1 in (i', i'))
  let fname = "Conjecture_" ++ show n ++ ".lean"
  writeFile (projDir proj </> fname) conjectureSrc
  lake <- elanBin "lake"
  (exitCode, out, err) <- readCreateProcessWithExitCode
    (proc lake ["env", "lean", fname]) { cwd = Just (projDir proj) } ""
  return $ case exitCode of
    ExitSuccess   -> Ok
    ExitFailure _ -> Failed (out ++ err)
