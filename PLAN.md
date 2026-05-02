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
  intros; simp_all [gAdd, gMult, fSqr, gEven, gOdd, gAdd1]
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
  `by intros; simp_all [<defs>]`, escalating to LLM-supplied proof body
  on failure, then to classical fallback
- Inline back-edge detection in `bftIO`: emits `Fold` nodes during
  construction so the IO-driven tree is finite by construction
  (without it, `bftIO` stack-overflows on essentially anything since
  it can't rely on `bftPure`'s laziness)
- Sharpened LLM prompt: requires the body of the let-chain to be a call
  with all-variable arguments, so it's foldable
- Benchmark harness (`bench/Main.hs`, `stack exec llm-bench`): runs
  three benchmarks, captures per-benchmark trace, reports stats
- 3/3 benchmarks pass with **all** LLM proposals Lean-verified:
  - `gEven(fSqr(x))`: 8 LLM 8/8 verified, 6 folds
  - `gAdd(gAdd(x, y), z)`: 2 LLM 2/2 verified, 3 folds
  - `gEq(gHalf(gDouble(n)), n)`: 2 LLM 2/2 verified, 3 folds

**Not yet:**
1. KMP (`fMatch` in `prog2`): blocked because the mutual recursion in
   `gM/gX/gN` passes `op/os` unchanged, so Lean's automatic structural
   termination can't find a measure. Fix: emit `termination_by`
   clauses with a custom lex measure.
2. Auto-prove tactic widening: nothing has tripped the LLM-as-prover
   path in benchmarks yet, but algebraic facts that need induction
   (e.g. `gAdd x Z ≡ x`) would. Once one shows up, consider
   `first | simp_all [defs] | (intros; induction <;> simp_all [defs])`
   before paying for an LLM proof call.
3. Distillation experiments — see "Why this matters" below.

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
