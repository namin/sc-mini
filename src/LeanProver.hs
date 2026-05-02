module LeanProver
  ( autoTactic
  , tryAuto
  ) where

import Data
import Types
import LeanEmbed (embedConjecture)
import LeanCheck (LeanProject, Verdict(..), verify)

-- The canned auto-prove tactic. Form:
--   by intros; simp_all
-- `intros` discharges any leading forall-quantifiers so simp_all can
-- pattern-match on concrete shapes. We deliberately do NOT pass the
-- program's function names as a simp set: the LLM's proposals are
-- almost always let-introductions, and let-elimination is a default
-- simp rule, so the conjecture closes via syntactic-equality-after-
-- substitution without needing function-body unfolding.
--
-- Avoiding function-name simp arguments also dodges Lean's
-- well-founded-vs-structural recursion divide: structurally-recursive
-- defs accept `simp_all [f]` happily, but mutually-recursive
-- well-founded defs (KMP-style) emit "Possibly looping simp theorem"
-- warnings or fail to unfold. Keeping the auto-tactic free of program
-- names sidesteps the issue entirely. Anything that genuinely needs
-- function unfolding falls through to LLM-as-prover, which can name
-- equation lemmas (`f.eq_def`, `f.eq_2`) explicitly.
autoTactic :: TypeEnv -> Program -> String
autoTactic _ _ = "by intros; simp_all"

-- Render `e ≡ e'` as a Lean conjecture with the auto-tactic as proof body
-- and ask Lean to check it. Returns the raw verdict so callers can decide
-- whether to escalate to the LLM (on Failed) or accept (on Ok).
tryAuto :: TypeEnv -> Program -> LeanProject -> Expr -> Expr -> IO Verdict
tryAuto env prog proj e e' =
  verify proj (embedConjecture env prog e e' (autoTactic env prog))
