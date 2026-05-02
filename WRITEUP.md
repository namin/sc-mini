# Lean as a trust boundary: an LLM-augmented supercompiler

A small experiment in LLM-driven program transformation, gated by a formal
verifier. What happens when you let a language model propose semantically-
meaningful rewrites for a compiler, and have a theorem prover check its
work? Some clean wins, some honest failures, and a conceptual pattern
that maps onto a small but growing research thread.

## The anti-KMP test

`sc-mini` is an educational supercompiler for SLL — a tiny first-order
functional language used in the supercompilation literature since
Sørensen's 1994 thesis. It comes with a published 64-page tutorial
(Klyuchnikov & Krustev, *The Monad Reader* 23, 2014). One thing the
authors are unusually candid about is what `sc-mini` doesn't do well.
They name a canonical failure case — the **anti-KMP test**:

```
gEven(fSqr(x))
```

`fSqr(x) = gMult(x, x)`; `gEven` checks parity. Conceptually this should
be easy: the parity of x² equals the parity of x. But sc-mini's
classical supercompile produces a residual program with **328 functions**.
For small inputs that residual is faster than the original; for big
inputs it's *slower*. The authors flag this as the canonical
demonstration of supercompilation's residual-blow-up problem and remark:
"Such an example can be found for each of the other existing
supercompilers."

Now run the same input through our LLM-augmented pipeline:

```
==> even-square
    sizes: orig=11  classical=328  llm=4
    n=12: orig 315 steps  classical 13  llm 13
```

**Four functions instead of 328**, at the same step count. Two orders
of magnitude smaller residual, on the literature's documented worst case.

This isn't an isolated win. On `gEq(gHalf(gDouble(n)), n)` — a
specification ("half-of-double is the identity, so this equality is
always True") — the LLM-augmented residual is **zero functions, zero
steps**: the entire computation collapses to the constant `True()`. On
`gReverse(gReverse(xs))` — list reverse is its own inverse — likewise:
**zero functions, zero steps**, regardless of input length. Classical
supercompilation can't reach these results; both reductions require
*semantic* facts about the program (parity preservation, function
inversion) that no syntactic rewrite system has access to.

The mechanism that makes this work: **the LLM proposes an equational
lemma about the program, supplies a Lean 4 proof, the proof is checked
by Lean's kernel, and verified lemmas are applied to rewrite the input
before the supercompiler starts driving.**

## Architecture

The setup is straightforward enough to fit in a paragraph:

```
Input task → Distillation pre-pass:
                ┌─ LLM proposes lemma + Lean proof
                ├─ Lean kernel checks the proof
                ├─ Pattern-match LHS against input subexpressions
                └─ If accepted, rewrite input → repeat (≤ 3 iterations)
              → Driving with HE whistle:
                ┌─ LLM proposes generalization at each whistle
                └─ Lean verifies via simp_all (or LLM-supplied proof)
              → Residuation → final compact program
```

Five layered mechanisms compose:

1. **Distillation pre-pass.** Before driving begins, ask the LLM for a
   useful lemma about the program and the input expression. Verify it.
   If it applies (LHS pattern-matches a subexpression), rewrite.
2. **Lemma chaining.** Verified lemmas accumulate in a per-supercompile
   context, inlined into subsequent Lean files so later proofs can use
   them as `rw [...]` rules. The LLM can decompose hard lemmas.
3. **Proof retry.** When Lean rejects an LLM proof, re-prompt with the
   error and ask for a fix to the same lemma. (One retry per lemma; this
   is what unlocks `half-of-double`'s second-stage proof.)
4. **Rejects tracking with conditional guidance.** Rejected proposals
   accumulate alongside verified ones and appear in subsequent prompts
   so the LLM doesn't re-propose broken lemmas. The prompt softens —
   "off-candidate helpers are okay" — only after a rejection.
5. **Rewriter modulo program unfolding.** A lemma about `gMult(x, x)`
   applies to a `fSqr(x)` subexpression because `fSqr(x) = gMult(x, x)`
   unfolds into shape. One step of unfolding during pattern matching
   absorbs the LLM's choice between equivalent lemma forms.

The whole extension is about 1200 lines of Haskell. The TCB consists
of Lean's kernel, the SLL→Lean embedding, the rewriter, and sc-mini's
underlying engine — none of which the LLM is part of. Anything the
LLM produces is filtered by the kernel; rejected proposals are
silently dropped.

## A concrete trace: half-of-double

Here's what an actual run of `gEq(gHalf(gDouble(n)), n)` looks like:

```
[distill] requesting lemma #1
[distill] LLM response:
  FORALL: n : Nat
  LHS: gHalf(gDouble(n))
  RHS: n
  PROOF:
  by induction n with
     | Z => rfl
     | S k ih => simp [gDouble, gHalf, gHalf1]; exact ih

[distill] lemma verified by Lean
[distill] applied: gEq(n, n)

[distill] requesting lemma #2 for: gEq(n, n)
[distill] LLM response: ...gEq(n, n) = True()...
[distill] proof failed (attempt 1/2), retrying
[distill] retry body: by
  induction n with
   | Z => simp [gEq, gEqZ]
   | S x ih => simp [gEq, gEqS, ih]
[distill] lemma verified by Lean
[distill] applied: True()

[distill] driving rewritten task: True()
```

Three things are happening here. First, the LLM proposes
`gHalf(gDouble(n)) = n` and a complete Lean proof. The proof is checked
by Lean's kernel — not by a separate decision procedure, just by reading
the LLM's `induction; rfl/simp` argument and verifying it type-checks.
The lemma applies; the input becomes `gEq(n, n)`.

Second, the LLM proposes `gEq(n, n) = True()`. Its first proof attempt
fails — `simp_all [gEq, gEqS, gEq]` doesn't reduce `gEq Nat'.Z Nat'.Z`
to `True()`. The system feeds Lean's error back to the LLM. The LLM
produces a working proof using explicit induction. The lemma applies.

Third, the input is now the constant `True()`. The supercompiler has
nothing to do; the residual program has zero functions, runs in zero
steps for any input.

This trace is the system's competence in microcosm: an LLM-supplied
proof closes a non-trivial inductive equation, the proof is checked
mechanically, and the verified rewrite collapses a computation to a
constant.

## Honest failure modes

Three benchmarks expose the limits of the approach:

**`add-commute`** (`gEq(gAdd(x, y), gAdd(y, x))` should reduce to
`True()`). The LLM correctly identifies the chain of helper lemmas it
needs (`gAdd(x, Z) = x`; `gAdd(x, S(y)) = S(gAdd(x, y))`; then
commutativity itself). The two helper sub-lemmas verify cleanly, get
added to the chain context. Commutativity itself doesn't — the LLM's
Lean proof attempts use invalid tactics (`introN` failures, mixing
Lean's stdlib `Nat` constructors with our custom `Nat'`, choosing
`simp only` where `simp` was needed). The retry helps sometimes; not
here. The benchmark exposes the dependency on LLM proof-writing
reliability.

**`length-distributes`** (`gLength(gAppend(xs, ys))` could be rewritten
to `gAdd(gLength(xs), gLength(ys))` — the homomorphism). The LLM
proposes this. Lean verifies it. The rewriter applies it. And the
result is *slightly slower than the original* — same asymptotic cost,
plus a constant factor for the gAdd. The lemma is true and provable,
but it's a *refactoring*, not an optimization: the RHS has more function
calls than the LHS (3 vs 2). The system has no built-in heuristic
distinguishing useful equational rewrites from no-ops. Honest limit:
"every verified lemma applied" isn't the same as "every applied lemma
helps."

**`kmp-aa`** (`fMatch(Cons(A, Cons(A, Nil)), s)` — KMP-style pattern
matcher). Structurally out of scope. The input has only one call
subexpression (`fMatch` itself); no useful semantic identity exists at
that level (you can't write a one-line equation that simplifies KMP).
Distillation has nowhere to apply. Result: same residual size as
without distillation, slower than classical.

A fourth benchmark, `eval-fold` (constant-folding for arithmetic
expressions over a recursive ADT), is informative for a different
reason: **it doesn't run at all**, in either the LLM or the classical
path. Classical's `supercompile` stalls for minutes on
`gEval(gFold(e))`. Our probing localized the problem to `gFold(e)`
alone — single g-function call on a symbolic ADT, no LLM, no Lean
overhead. The pattern: `gFold` has *two* recursive calls in its
`AAdd` arm:

```
gFold(AAdd(e1, e2)) = gFoldAdd(gFold(e1), gFold(e2));
```

Binary self-recursion creates depth-explosive process trees that
sc-mini's classical supercompile doesn't handle. The original tutorial
documents exactly this:

> There is no similar indirect limit to the growth of graph depth
> (apart for ensuring it is finite), and this can result in very large
> residual programs.
>
> *Exercise 18.* Try to find such examples for SC Mini.

We literally found Exercise 18's example. The bottleneck is the
upstream educational supercompiler, not our LLM extension. (Tier-1
list operations like `gReverse` and `gAppend` use single recursion and
work fine, which is why `reverse-involution` and `length-distributes`
both run cleanly.)

## What this is not

The honest framing of this work:

- **It is a toy.** SLL is a research toy language; benchmarks fit on a
  page; sc-mini is from a tutorial, explicitly meant to be illustrative.
  Real Haskell programs use higher-order functions, polymorphism, and
  ADTs we don't have. To handle real programs we'd need a richer source
  language — which the original tutorial authors call "PhD-level work."

- **It is not a general solution to residual blow-up.** It addresses
  *specific* cases where a useful Lean-verified equation exists at the
  input's call-subexpression level, the LLM finds it, the LLM proves
  it, and the RHS is genuinely simpler. When all four hold, we win.
  When any one fails, we tie classical or fall through.

What it *is*: a small empirical demonstration that the architectural
pattern — LLM proposes verified rewrites, kernel checks, transformer
applies what passes — works on the literature's canonical educational
language, beats the literature's canonical worst case (anti-KMP), and
is small enough to fit in a single document.

## Reproducing this

The codebase is at the project repository. Two harnesses make all real
Bedrock calls:

```
stack build
stack exec llm-bench       # all default benchmarks (correctness)
stack exec llm-perf        # performance comparison
```

Both accept benchmark names to run a subset:

```
stack exec llm-perf reverse-involution add-assoc
```

Per-benchmark stderr traces are kept under `bench/results/<name>.trace`
for inspection. Each run makes ~10–30 Bedrock calls depending on which
benchmarks; cost is a few cents and a minute or two of wall time.

Prerequisites: GHC 9.4.8 + stack, Lean 4.29.1 via elan, AWS credentials
with Bedrock access for the Sonnet 4.6 model.

Empirical landing position (typical run; outcomes have run-to-run
variance because the LLM is non-deterministic):

| Benchmark           | Classical  | LLM (this work)              |
|---------------------|------------|------------------------------|
| even-square         | 328 / 13   | **4 / 13**  (matches speed, 82× smaller) |
| add-assoc           | 4 / 22     | 4 / 22  (ties)               |
| half-of-double      | 2 / 13     | **0 / 0**  (beats classical) |
| reverse-involution  | 48 / 42    | **0 / 0**  (beats classical) |
| add-commute         | 207 / 25   | 14 / 67  (matches original)  |
| length-distributes  | 4 / 22     | 10 / 33  (regresses)         |
| kmp-aa              | 9          | 37  (out of scope)           |

(`x / y` reads as residual function count / interpreter steps for a
representative input.)

