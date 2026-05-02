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
  / `simp [...]` invocations.
- Proof retry on verification failure: when Lean rejects an
  LLM-supplied proof, the system reprompts the LLM with the failure
  output and asks for a fixed proof of the *same* lemma (preserving
  forall/lhs/rhs). Up to `distillProofRetries = 1` retry per lemma,
  costing one Bedrock call.
- Rejects tracking + conditional guidance: rejected proposals (with
  the Lean error message) accumulate alongside verified ones, and
  appear in subsequent prompts so the LLM doesn't re-propose the
  same broken lemma. The "you may propose helper sub-lemmas" license
  is conditional on whether previous attempts have failed: the first
  iteration prompt is strict on-candidate; after a rejection, the
  prompt opens up to off-candidate helpers (which then become
  available as `rw` rules in the chain).
- Smarter rewriter modulo program unfolding: when a verified lemma's
  LHS doesn't syntactically match a subexpression of the input, the
  rewriter tries one step of f-call/g-call unfolding before giving
  up. So a lemma about `gMult(x, x)` will apply to a subexpression
  `fSqr(x)` because `fSqr(x) = gMult(x, x)` unfolds into shape. The
  rewrite still replaces the original (pre-unfold) subexpression,
  not the unfolded form.

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

After all five mechanisms (chaining, retry, rejects tracking,
conditional guidance, smarter rewriter), the system's behavior on the
seven-benchmark suite is:

| Benchmark            | Classical          | LLM (typical run)              |
|----------------------|--------------------|--------------------------------|
| even-square          | 328 fns / 13 steps | **4 fns / 13 steps** (variance — see below) |
| add-assoc            | 4 / 22             | 4 / 22 (matches)               |
| half-of-double       | 2 / 13             | **0 / 0** (beats classical)    |
| kmp-aa               | 9 / —              | 37 / — (out of scope)          |
| add-commute          | 207 / 25           | 14 / 67 (matches original)     |
| reverse-involution   | 48 / 42            | **0 / 0** (beats classical)    |
| length-distributes   | 4 / 22             | 10 / 33 (regresses)            |

The cleanest wins:

- **half-of-double**: LLM chains `gHalf(gDouble(n)) = n` and
  `gEq(n, n) = True()` to reduce the input to a constant. Zero
  residual functions, zero step count.
- **reverse-involution**: LLM proposes
  `gReverse(gReverse(xs)) = xs` on the first iteration, Lean verifies
  the inductive proof, the rewriter applies it, the input collapses
  to the bare variable `xs`. Zero functions, zero steps regardless
  of input list length. Crucially this isn't Peano arithmetic — it's
  a list functor identity, demonstrating the approach generalizes
  beyond the original numeric demos.
- **even-square** (when it works): LLM proposes
  `gEven(fSqr(x)) = gEven(x)` (or the more general
  `gEven(gMult(x, x)) = gEven(x)`, handled by the smarter rewriter),
  Lean verifies, the rewriter applies it, supercompiler drives
  `gEven(x)` to 4 functions. Same speed as classical, 82x smaller
  residual.

The informative failures:

- **kmp-aa**: input has only one call subexpression (`fMatch` itself).
  No useful semantic lemma exists at the candidate level. Out of
  scope for distillation as currently formulated.
- **add-commute**: LLM correctly identifies the chain it needs (sub-
  lemmas `gAdd(x, Z) = x` and `gAdd(x, S(y)) = S(gAdd(x, y))`, then
  commutativity itself), and the rejects-tracking nudges it toward
  helpers after direct fails. The two helper sub-lemmas verify
  cleanly; commutativity itself doesn't — the LLM's Lean proof
  attempts use invalid tactics or fail in ways even a retry doesn't
  catch.
- **length-distributes**: LLM proposes the homomorphism
  `gLength(gAppend(xs, ys)) = gAdd(gLength(xs), gLength(ys))`. The
  proof verifies. The rewriter applies it. But the residual gets
  *slightly larger and slower*: LHS has 2 function calls, RHS has 3,
  and the asymptotic cost of computing both sides is the same (both
  O(m+n) for lists of lengths m and n). The lemma is true and the
  rewriter applies it correctly — but it's a *refactoring*, not an
  optimization. The system has no way to distinguish the two and
  applies any verified lemma. This surfaces a previously-unstated
  assumption: distillation only helps when the lemma's RHS is
  *substantively cheaper* than the LHS, not just structurally
  different. The prompt does say "RHS structurally simpler" but the
  LLM overrode that with the canonical homomorphism equation.

## The variance floor

Even-square outcomes vary across runs because the LLM picks between
equivalent lemma forms (e.g. `gEven(fSqr(x)) = gEven(x)` vs
`gEven(gMult(x, x)) = gEven(x)`), and **its proofs use invalid Lean
tactics often enough that a single retry isn't always sufficient**.
Observed proof failures across runs include:

- `induction n with | zero => ... | succ n ih => ...` — Lean stdlib
  `Nat` constructors used instead of our `Nat'`'s `Z`/`S`.
- `simp only [...]` where `simp [...]` (without `only`) was needed
  to reduce the goal far enough.
- `by unfolding` — not a real Lean tactic (the LLM may be conflating
  `unfold` with mathlib's `unfolding` notation).
- `True'` instead of `True` — over-application of the prime
  convention used for type names.

These are LLM-side errors that more architecture wouldn't help.
Multi-sample proposals (have the LLM produce N candidate proofs per
turn and verify each) would damp the variance at the cost of more
Bedrock calls.

## How the pieces interact

The five mechanisms compose:

- **Chaining + retry** unlocks `half-of-double` (chain of two
  inductive lemmas, second proof fails first try and succeeds on
  retry).
- **Conditional guidance** prevents the LLM from drifting to
  off-candidate sub-lemmas when a direct lemma is available
  (`even-square`, `add-assoc`).
- **Rejects tracking** lets the LLM see its own past failures and
  adapt — observed clearly on `add-commute`, where the LLM's third
  iteration explicitly says "the previous attempt failed because it
  tried to prove it directly with `simp`. Let me propose a helper".
- **Smarter rewriter** (modulo unfolding) absorbs the LLM's choice
  of lemma form: `gEven(gMult(x, x)) = gEven(x)` and
  `gEven(fSqr(x)) = gEven(x)` are both useful for the same input
  whereas previously only the latter applied.

The remaining variance and the `add-commute` holdout point at
LLM-side proof unreliability, not at the architecture.

**Not yet:**
1. **Reject lemmas that don't reduce work**: pre-filter LLM proposals
   before sending to Lean — if the RHS has the same or more function
   applications than the LHS, skip the verification call. Surfaced
   by `length-distributes`. The LLM's "structurally simpler" prior
   is loose enough that it'll propose true-but-non-optimizing
   equations like the length-of-append homomorphism. A simple syntactic
   check at our side is more reliable than a prompt instruction.
   (Could be too conservative for cases like `add-assoc` where the
   call counts are equal but the rewrite still helps the supercompiler
   fold; need to think about the right metric.)
2. **Multi-sample lemma proposals**: have the LLM emit N candidate
   proofs per turn and verify each. Damps variance from
   non-deterministic proof writing (the dominant remaining failure
   mode). Cost-multiplier on Bedrock spend; would likely close
   `add-commute` and stabilize `even-square`.
3. **Try every lemma in the chain against the input on each
   iteration**: currently we only try the most recently verified
   lemma against the current expression. A re-application pass would
   pick up cases where an earlier off-target lemma becomes
   on-target after the input shape changes.
4. **Oscillation detection**: detect when a lemma rewrites in one
   direction and a subsequent lemma reverses it. Doesn't unblock
   benchmarks but prevents wasted Bedrock calls.
5. **Persistent lemma library**: cache verified lemmas across
   supercompile runs so each program "learns" over time.
6. **Auto-prove tactic widening**: nothing has tripped the
   LLM-as-prover path with an Ok verdict yet on the existing
   benchmarks. Real induction-needing conjectures would benefit
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
