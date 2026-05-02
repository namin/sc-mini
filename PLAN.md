# LLM-Augmented Supercompiler: Plan

## The idea

A supercompiler transforms a program by symbolically evaluating it
(driving), detecting divergence (whistle), generalizing to ensure
termination, and folding into a residual program. The residual is
equivalent to the original but often faster.

The hard problem is generalization. Classical most-specific
generalization (msg) is purely syntactic and often too aggressive.
An LLM can propose bolder transformations — accumulator introduction,
eureka lemmas, shared subexpression extraction — but those need proofs.

The thesis: the LLM proposes transformations AND generates Lean proofs
that they're correct. Lean checks the proofs. The supercompiler
doesn't need to trust the LLM at all.

## Why not verify via supercompilation

Supercompilation can prove equivalence: supercompile both sides, check
if the residuals match. But this is circular — if the classical
supercompiler could already prove the equivalence, we didn't need the
LLM to propose it. The LLM is only useful when it goes beyond what
the classical algorithm can do, which is exactly when the classical
algorithm can't verify it.

## Architecture

```
Whistle fires: ancestor a, current e
                |
       [LLM proposes e' (SLL only)]
                |
       [auto-prove: by intros; simp_all [<defs>]]
          /            \
      exit 0         exit 1
     (valid)        (auto-prove failed)
        |               |
     use e'    [LLM supplies a Lean proof body]
                        |
                  [verify with lean]
                  /            \
              exit 0         exit 1 (≤ N retries)
                 |              |
              use e'    fall back to classical
```

The LLM is responsible only for proposing `e'` in SLL — it has to feed
back into the supercompiler as the next configuration to drive. The
proof is a separate concern attempted in two stages:

1. **Auto-prove.** One canned tactic, one `lean` call:
   `by intros; simp_all [<every f-def, every g-clause>]`. This
   dispatches let-introductions and any equivalence that's
   definitionally true after unfolding — the common case.
2. **LLM-as-prover.** Only if auto-prove fails: re-prompt the LLM with
   the conjecture and the failure stderr, asking for a `by …` block.
   Verify with Lean. ≤ N retries; on persistent failure, fall through
   to classical generalization.

We materialize a per-run lake project: `Program.lean` is built once
into a cached `Program.olean`; each verification writes a fresh
`Conjecture_<n>.lean` (which `import`s `Program`) and runs
`lake env lean Conjecture_<n>.lean`.

The embedding of SLL into Lean is mechanical given a hand-written
`TypeEnv` per program (data declarations + function signatures); we
don't try to infer types. This keeps the boundary clean and avoids
ambiguity bail-outs.

## The Lean embedding

Given an SLL program:
```
gAdd(Z(), y) = y;
gAdd(S(x), y) = S(gAdd(x, y));
```

Generate Lean:
```lean
inductive Nat' where
  | Z : Nat'
  | S : Nat' → Nat'

def gAdd : Nat' → Nat' → Nat'
  | .Z, y => y
  | .S x, y => .S (gAdd x y)
```

SLL is first-order and total (for terminating inputs), so the
translation is direct. Constructors become Lean inductives,
g-functions become Lean pattern-matching functions, f-functions
become Lean definitions.

When the LLM proposes `e'`, we render the conjecture as:
```lean
import Program

theorem gen_ok : forall (x : Nat'), ⟦e⟧ = ⟦e'⟧ := by
  intros; simp_all
```

If `simp_all` discharges it, we accept `e'`. Otherwise we ask the LLM
for a `by …` block, splice it in, and re-verify. Either way the trust
boundary is Lean's kernel — we don't need to understand the proof or
trust the LLM.

## Where we are

**Done:**
- Classical supercompiler (sc-mini) on GHC 9.4.8
- Homeomorphic embedding whistle with ancestor tracking
- Classical generalization (extractArg) as fallback
- AWS Bedrock integration (Claude Sonnet 4.6)
- LLM generalization wired into the supercompiler
- SLL-to-Lean embedding (`LeanEmbed.hs`): renders inductives, mutual
  blocks, expressions, and conjectures from a hand-written `TypeEnv`
- Per-run lake project + verifier (`LeanCheck.hs`): one `Program.olean`
  built once, per-call `Conjecture_<n>.lean` checked via `lake env lean`
- Two-stage proof strategy (`LeanProver.hs`): canned auto-tactic
  `by intros; simp_all` (no defs list — let-elimination is a default
  simp rule, and avoiding function-name simp args sidesteps the
  well-founded-vs-structural recursion divide). Escalates to
  LLM-supplied proof body on failure, then to classical fallback.
- Inline back-edge detection in `bftIO`: emits `Fold` nodes during
  construction so the IO-driven tree is finite by construction
  (without it, `bftIO` stack-overflows on essentially anything since
  it can't rely on `bftPure`'s laziness)
- Sharpened LLM prompt: requires the body of the let-chain to be a call
  with all-variable arguments, so it's foldable
- `partial def` opt-in via `funPartial :: [Name]` in `TypeEnv` for
  functions whose termination Lean can't see automatically (e.g.
  KMP-style mutual recursion). Inductives derive `Inhabited`
  unconditionally so partial defs have a default value to fall back
  on.
- Driving robustness fixes (`Driving.hs`): missing g-clause for a
  constructor returns `Stop` (was a `head []` crash); the `inject`
  helper handles `Stop` and `Decompose` cases (was non-exhaustive).
  These shielded the supercompiler from ill-typed expressions that
  multi-typed programs (KMP) trigger.
- Benchmark harness (`bench/Main.hs`, `stack exec llm-bench`): runs
  four benchmarks, captures per-benchmark trace, reports stats. Pass
  criterion is termination + sane residual size (not "every proposal
  Lean-verified" — auto-prove failures are recoverable via classical
  fallback).
- Name-collision fix in `bftIO`: after the whistle, LLM-proposed
  expressions can introduce variables (e.g. `v5`, `v6`) that collide
  with the next prefix of the supply. When `scrutinize` later draws
  fresh pattern vars from the supply, those names get conflated with
  pre-existing free vars of different types — producing the type-bogus
  expressions that Lean was catching and rejecting on KMP. Filtering
  the LLM-introduced names out of the supply (`ns \\ vnames gen`)
  before recursing fixes it at the source.
- 4/4 benchmarks pass with **all** LLM proposals Lean-verified:
  - `gEven(fSqr(x))`: ~22 fns, ~5 LLM calls 5/0 auto-prove
  - `gAdd(gAdd(x, y), z)`: ~8 fns, 1 LLM call 1/0 auto-prove
  - `gEq(gHalf(gDouble(n)), n)`: ~14 fns, 1 LLM call 1/0 auto-prove
  - `fMatch(Cons(A, Cons(A, Nil)), s)` (KMP): ~37 fns, 4 LLM calls
    4/0 auto-prove (no fallbacks)

- Performance comparison harness (`bench/Perf.hs`, `stack exec
  llm-perf`): runs each benchmark through `intC` on a range of
  concrete inputs for three programs (original / classical /
  LLM-supercompiled) and reports step counts plus speedup ratios. Also
  serves as a correctness check (asserts all three return the same
  value).

## Empirical finding from the perf harness

Across the four benchmarks, **LLM-supercompiled residuals do not
reduce step counts vs. the original program**, while
classical-supercompiled residuals do (up to 24x faster on
`even-square` at x=12, ~5x on `half-of-double`). All three variants
compute the same values, so the LLM path is correct — it just isn't
faster.

The reason is structural: the LLM currently proposes *let-
introductions* (extract a subexpression and bind it to a fresh var).
Those preserve operation count. The transformations that actually
speed things up (e.g. "`gEven(fSqr(x))` has the same parity as
`gEven(x)`") are *eureka lemmas* — assertions about program behaviour
that need a separate proof, not just a rename. Classical
supercompilation gets some speedups by aggressively unfolding (the
~24x on even-square came with a 328-function residual); the LLM with
HE produces compact residuals (22 functions) but at the cost of
preserving the original program's runtime shape.

This validates the original PLAN framing: the LLM is only useful
when it goes beyond what classical can do — and "let-introduction
under HE" isn't beyond classical. The next step is therefore
distillation: ask the LLM for actual lemmas, prove them in Lean,
rewrite the program using them.

**Not yet:**
1. Distillation experiments. The natural next direction given the
   perf finding above. Concretely: when the supercompiler gets stuck
   (HE fires repeatedly without producing a foldable shape, or the
   residual matches the original in step count), prompt the LLM for
   a *lemma* — e.g. `forall x, gEven(fSqr(x)) = gEven(x)` — plus a
   Lean proof. If Lean accepts, register the lemma and rewrite
   matching subexpressions. This is the move that gets the LLM
   beyond what classical can do.
2. Auto-prove tactic widening: nothing has tripped the LLM-as-prover
   path with an Ok verdict yet across the four benchmarks. Real
   induction-needing conjectures (e.g. `gAdd x Z ≡ x`) would benefit
   from a tactic like
   `first | simp_all | (intros; induction <;> simp_all)`.

## Why this matters

The LLM doesn't need to be reliable. It needs to sometimes be
brilliant. Lean ensures we only keep the brilliant parts. Every
accepted transformation carries a machine-checked proof, which is
a stronger guarantee than the classical algorithm provides (the
classical algorithm is "correct by construction" but only because
it's too conservative to be wrong).

The long-term goal is distillation (Hamilton 2007): discovering
lemmas that enable super-linear speedups. An LLM that can propose
lemmas with Lean proofs makes distillation practical for arbitrary
programs.
