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
- Distillation pre-pass (`Distillation.hs`): before driving begins,
  the LLM is asked for one or more eureka lemmas about the program +
  input expression. Each candidate is verified via the existing
  `LeanCheck.verify` pipeline (induction proofs go through here, not
  through the auto-prove block). Verified lemmas are pattern-matched
  against subexpressions of the input via a one-sided unifier
  (lemma's quantified vars as metavariables); on a match, the input
  is rewritten with the lemma's RHS. Iterates up to a small budget
  (`maxDistillLemmas = 3` LLM calls per supercompile).
- Lemma chaining: verified lemmas accumulate across iterations of the
  pre-pass. They're (a) inlined at the top of subsequent
  `Conjecture_<n>.lean` files (with their already-checked proofs) so
  Lean recognizes them as available rewrite rules, and (b) listed in
  the prompt to the LLM so it can reference them by name in `rw [...]`
  / `simp [...]` invocations. The prompt also encourages
  decomposition: if the lemma the LLM ideally wants to state needs a
  sub-lemma, propose the sub-lemma this turn, build the chain.
- Proof retry on verification failure: when Lean rejects an
  LLM-supplied proof, the system reprompts the LLM with the failure
  output and asks for a fixed proof of the *same* lemma (preserving
  forall/lhs/rhs). Up to `distillProofRetries = 1` retry per lemma,
  costing one Bedrock call. Addresses the LLM-non-determinism
  observed in the chaining-only run, where the LLM sometimes wrote
  `simp only [...]` (failed) instead of `simp [...]` (worked) for the
  same target lemma.

## Empirical findings from the perf harness

The perf harness (`stack exec llm-perf`) compares the original program,
the classical-supercompiled residual, and the LLM-supercompiled
residual on concrete inputs.

**Without distillation** the LLM path produced compact, correct,
machine-checked residuals — but with the *same step count as the
original program*, while classical achieved up to 24x speedup. The
gap was structural: the LLM proposes let-introductions (which
preserve operation count); classical achieves speedups by aggressive
unfolding (at the cost of large residuals: 328 functions on
even-square).

**With distillation enabled (basic)** the LLM finds eureka lemmas on
two of the four benchmarks, and Lean verifies their proofs.

**With lemma chaining + proof retry** added on top, distillation
chains *two* lemmas on `half-of-double` and produces a residual that
beats classical:

| Benchmark        | No distillation        | Basic distillation     | + chaining + retry        |
|------------------|------------------------|------------------------|---------------------------|
| add-assoc        | 8 fns, k=10: 32 steps  | 4 fns, 22 steps        | 4 fns, 22 steps           |
| half-of-double   | 14 fns, n=12: 64 steps | 2 fns, 13 steps        | **0 fns, 0 steps**        |

The half-of-double case is the cleanest example of the full
pipeline:

1. LLM proposes `forall n, gHalf(gDouble(n)) = n` and proves it on
   first try. Rewriter applies it: input becomes `gEq(n, n)`.
2. LLM proposes `forall n, gEq(n, n) = True()`. First proof attempt
   uses `simp_all [gEq, gEqS, gEq]` and *fails* (`gEq Nat'.Z Nat'.Z`
   doesn't reduce). The system re-prompts with the Lean error; the
   LLM produces a working proof: `induction n with | Z => simp [gEq,
   gEqZ] | S x ih => simp [gEq, gEqS, ih]`. Rewriter applies it:
   input becomes `True()`.
3. Driving has nothing to do; the residual is the constant `True()`,
   zero functions.

This is the first benchmark where the LLM-augmented supercompiler
produces a *smaller* residual than classical — and it's the kind of
result classical can't reach because classical doesn't know that
"halving twice the value gives the value back." That's a semantic
fact about the *equivalence relation*, not the program structure,
and only a Lean-checked lemma can put it on the table.

**Distillation still doesn't help on the other two**:

- `even-square`: the LLM proposes `gEven(fSqr(x)) = gEven(x)` and
  sub-lemmas like `gEven(gAdd(x, x)) = True`, but the proofs all
  hit type/syntax issues. Across 3 proposals × 2 retry attempts each,
  none verified. The chain stays empty. Real fix likely needs
  multiple attempts per lemma plus better proof-fixing prompts.
- `kmp-aa`: lemmas verify but don't pattern-match the input
  expression's shape. Targeted prompting ("propose a lemma whose LHS
  is a subexpression of this exact term") would help.

The empirical answer to "is the LLM-augmented supercompiler
beneficial": **yes, with distillation, on benchmarks where the
proof-search succeeds — and on `half-of-double` it now produces a
strictly smaller residual than classical**. When the LLM can't prove
the lemmas, the system gracefully falls back.

## How lemma chaining + proof retry interact

Looking at the half-of-double trace, **the retry is what
makes the chain productive**. Without retry, the second lemma
(`gEq(n, n) = True()`) fails its first proof attempt and gets
discarded, and we never see the chain finish. With retry, the LLM
gets a second chance with the Lean error in hand and produces a
working proof. Without chaining, the working proof of
`gEq(n, n) = True()` would have been wasted — there'd be no
already-verified `gHalf(gDouble(n)) = n` to reduce the input to
`gEq(n, n)` in the first place. Both pieces are necessary.

The two also compose well budget-wise: 3 lemma proposals × 2 attempts
per lemma = 6 Bedrock calls maximum per supercompile. In practice
half-of-double used 5 (2 successful first-tries + 1 retry), which is
modest given the result.

Where this approach hits its limit, on the current benchmarks:

- `even-square` still doesn't unlock because the *right* sub-lemma
  chain is intricate (parity-of-gMult needs parity-of-gAdd which
  needs gAdd-with-Z, etc.) and the LLM tends to propose the *wrong*
  big lemma (e.g. `gEven(gAdd(x,x)) = True`, which it then can't
  prove because it's right but proving it requires the parity
  reasoning we wanted in the first place). A few directions:
  - More retry attempts (currently 1; bump to 2-3)
  - Targeted prompting ("prove this specific sub-goal")
  - A "decompose this" prompt that asks the LLM to enumerate sub-lemmas
- `kmp-aa`: lemmas verify but don't pattern-match the input. The
  targeted-prompting fix is the right one — narrow the LLM's
  attention to subexpressions of the actual input.

**Not yet:**
1. **Targeted prompting**: ask for a lemma about a specific
   subexpression rather than "anything useful". Would help `kmp-aa`.
2. **Bump proof-retry budget**: currently 1 retry per lemma. 2-3
   would give the LLM more shots at fixing tricky proofs and might
   unlock `even-square`'s sub-lemma chain.
3. **Oscillation detection**: detect when a lemma rewrites in one
   direction and a subsequent lemma reverses it. Doesn't unblock
   benchmarks but prevents wasted Bedrock calls.
4. **Persistent lemma library**: cache verified lemmas across
   supercompile runs so each program "learns" over time.
5. **Auto-prove tactic widening**: nothing has tripped the
   LLM-as-prover path with an Ok verdict yet across the four
   benchmarks. Real induction-needing conjectures (e.g.
   `gAdd x Z ≡ x`) would benefit from a tactic like
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
