module LeanProver
  ( autoTactic
  , tryAuto
  ) where

import Data
import Types
import LeanEmbed (embedConjecture)
import LeanCheck (LeanProject, Verdict(..), verify)

import Data.List (intercalate, nub)

-- All function names (f-defs and g-def groups) in the program. Used as the
-- simp_all lemma set — Lean's auto-generated equation lemmas for these
-- names give simp the means to unfold our definitions.
allFunNames :: Program -> [Name]
allFunNames (Program fs gs) =
  nub $ [n | FDef n _ _ <- fs] ++ [n | GDef n _ _ _ <- gs]

-- The canned auto-prove tactic. Form:
--   by intros; simp_all [gAdd, gMult, fSqr, ...]
-- `intros` discharges any leading forall-quantifiers so simp_all can
-- pattern-match on concrete shapes; the lemma list unfolds f's and g's.
-- Sufficient for any equivalence that's definitionally true after
-- unfolding (the common case: `Let`-introductions of subexpressions).
-- Insufficient for anything that needs induction; the LLM steps in for
-- those.
autoTactic :: TypeEnv -> Program -> String
autoTactic _ p =
  let names  = allFunNames p
      lemmas = if null names then "" else " [" ++ intercalate ", " names ++ "]"
  in "by intros; simp_all" ++ lemmas

-- Render `e ≡ e'` as a Lean conjecture with the auto-tactic as proof body
-- and ask Lean to check it. Returns the raw verdict so callers can decide
-- whether to escalate to the LLM (on Failed) or accept (on Ok).
tryAuto :: TypeEnv -> Program -> LeanProject -> Expr -> Expr -> IO Verdict
tryAuto env prog proj e e' =
  verify proj (embedConjecture env prog e e' (autoTactic env prog))
