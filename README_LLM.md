# LLM-Augmented Supercompiler

Companion to `PLAN.md` (vision) and `DESIGN_LEAN.md` (embedding scheme).
This file describes what's implemented, how to run it, and how to read
the results.

## What this is

`sc-mini` extended with two new entry points alongside the existing
`supercompile` and `supercompileIO`:

- `supercompileIOWithTypes :: TypeEnv -> Task -> IO Task` — the same
  HE-whistle-based supercompiler, except every LLM-proposed
  generalization `e ≡ e'` must be checked by Lean before being accepted.
- The `bench/Main.hs` harness, exposed as the `llm-bench` executable.

The trust boundary is Lean's kernel: the LLM proposes an SLL `e'`; we
translate `e` and `e'` into Lean and ask Lean (via bare `simp_all`,
which has let-elimination as a default rule) to discharge the
conjecture `⟦e⟧ = ⟦e'⟧`. If Lean accepts, the LLM proposal is taken.
If Lean rejects, we re-prompt the LLM for a Lean proof body; if that
also fails to verify, we fall back to `classicalGeneralize` — the
same strategy the pure path uses. **Lean rejection is a feature, not
a failure mode**: it routes around proposals that would have been
unsound (e.g. type-bogus expressions arising from the supercompiler's
untyped substitution on multi-typed programs).

## Architecture

```
LLMSupercompiler.bftIO  ←  threads a Whistle callback
   │
   ├─ findFold hist e          → emit Fold node, no LLM call
   ├─ HE fires?                → Whistle:
   │                              ┌─ unverified path: LLM only
   │                              └─ verified path:
   │                                    LLM proposes e'
   │                                    LeanProver.tryAuto
   │                                       Ok    → accept
   │                                       Fail  → llmProveBody → verify
   │                                                  Ok   → accept
   │                                                  Fail → classicalGeneralize
   │                              budget exhausted   → classicalGeneralize
   └─ otherwise                  → drive
```

Modules (all under `src/`):

| Module             | Responsibility |
|--------------------|----------------|
| `Types.hs`         | `TypeEnv` (data decls + function signatures) |
| `LeanEmbed.hs`     | Render `Program` and conjectures to Lean source |
| `LeanCheck.hs`     | Lake-project lifecycle, `verify` shells out to `lake env lean` |
| `LeanProver.hs`    | The canned auto-prove tactic and `tryAuto` |
| `LLMSupercompiler.hs` | Whistles, prompt construction, integration with `bftIO` |
| `Bedrock.hs`       | AWS SigV4 + Bedrock invoke for Claude |

The `bftIO` change worth flagging: it now does **inline back-edge
detection**. Before recursing into a sub-expression, it checks if the
expression is a renaming of any ancestor in `hist`; if so, it emits
`Fold` directly. This is what `foldTree` does post-hoc on the lazy
`bftPure` tree, but `bftIO` needs the tree to be finite by construction
(IO is strict — without inline folds it stack-overflows on most inputs).

## Per-program type information

SLL is monomorphic but untyped on the page. To embed in Lean we need
typed inductives. Rather than infer types (a fragile bail-out hazard)
the embedding consumes a hand-written `TypeEnv` next to each program:

```haskell
prog1Types :: TypeEnv
prog1Types = TypeEnv
  { typeDefs =
      [ DataDef "Nat"  [CtrDef "Z" [], CtrDef "S" [TyCon "Nat"]]
      , DataDef "Bool" [CtrDef "True" [], CtrDef "False" []]
      ]
  , funSigs =
      [ ("gAdd",  ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      , ...
      ]
  , funPartial = []
  }
```

`Demonstration.hs` carries `prog1Types`, `prog2Types`, `prog2aTypes`,
and `prog3Types`.

The `funPartial :: [Name]` field is an opt-in list of function names
that should be emitted as `partial def` rather than `def` in Lean.
Use it for functions whose termination Lean can't see automatically —
KMP's `gM/gX/gN` are mutually recursive without a structurally
decreasing measure (gN restarts from the original pattern), so
`prog2Types` declares them partial. Partial definitions don't get
equation lemmas in the simp set, but our auto-prove only needs
let-elimination (not function unfolding), so partial functions still
verify cleanly. Inductives are emitted with `deriving Inhabited`
unconditionally so partial defs have a default-value fallback.

## Prerequisites

- GHC 9.4.8 + stack (via ghcup; project uses lts-21.25).
- Lean 4.29.1 + lake at `~/.elan/bin/`.
  The first lake build per supercompile run takes 1–2 s; subsequent
  verifications reuse the prebuilt `Program.olean`.
- AWS credentials at `~/.aws/credentials` with Bedrock invoke
  permission for `us.anthropic.claude-sonnet-4-6` in `us-east-1`.
  Each whistle = 1 LLM call (or 2 if the auto-prove fails and we ask
  for a proof).

## Running the benchmarks

Two harnesses, both make real Bedrock calls:

```
stack build
stack exec llm-bench   # correctness/verification harness (4 benchmarks)
stack exec llm-perf    # performance comparison: orig vs classical vs LLM
```

Expected output (numbers vary because the LLM is non-deterministic):

```
Running LLM-supercompiler benchmarks (real Bedrock calls).
Per-benchmark stderr traces under bench/results/

==> even-square
    residual: gg1(x)
    functions: 22 (expected 5-30)
    whistles: 5  folds: 6  llm: 5  auto-prove: 5 ok / 0 fail  llm-proof: 0  budget: 0
    PASS
==> add-assoc
    residual: gg1(x, y, z)
    functions: 8 (expected 5-25)
    whistles: 1  folds: 3  llm: 1  auto-prove: 1 ok / 0 fail  llm-proof: 0  budget: 0
    PASS
==> half-of-double
    residual: gg1(n)
    functions: 14 (expected 5-30)
    whistles: 1  folds: 3  llm: 1  auto-prove: 1 ok / 0 fail  llm-proof: 0  budget: 0
    PASS
==> kmp-aa
    residual: ff1(s)
    functions: 37 (expected 5-40)
    whistles: 4  folds: 4  llm: 4  auto-prove: 4 ok / 0 fail  llm-proof: 0  budget: 0
    PASS

Summary: 4/4 passed.
```

A benchmark passes if the supercompile terminates, the residual's
function count falls in the documented range, and the safety cap on
whistle iterations isn't tripped. **Lean's verdict counts (`auto-prove
ok / fail`, `llm-proof`) are reported for transparency, not as a pass
gate** — when Lean rejects an LLM proposal, the supercompiler falls
back to classical generalization (correct by construction), so the
residual is still valid.

The full per-benchmark stderr trace is preserved at
`bench/results/<name>.trace` so you can inspect ancestor/current pairs,
LLM responses, and verification verdicts after the fact.

## Performance comparison

`stack exec llm-perf` runs the same four benchmarks but does the
*counting* version: for each benchmark, it computes three programs —
the original input, the classical-supercompile residual (size-bound
whistle, `Supercompiler.supercompile`), and the LLM-supercompile
residual (HE whistle, `supercompileIOWithTypes`) — then runs each
through `intC` (the counting interpreter) on a series of concrete
inputs and reports step counts and ratios.

Sample output (with distillation, lemma chaining, and proof retry):

```
==> even-square    (distillation: gEven(fSqr(x)) = gEven(x) applied)
    sizes: orig=11  classical=328  llm=4
    input    |  orig  |  class |   llm  | cls/orig |  llm/orig | llm/cls
    ---------+--------+--------+--------+----------+-----------+--------
    12       |    315 |     13 |     13 |    0.04  |    0.04   |   1.00

==> add-assoc      (distillation: associativity lemma applied)
    sizes: orig=11  classical=4  llm=4
    10       |     32 |     22 |     22 |    0.69  |    0.69   |   1.00

==> half-of-double (distillation: chain of two lemmas collapses to True())
    sizes: orig=14  classical=2  llm=0
    12       |     64 |     13 |      0 |    0.20  |    0.00   |   0.00

==> kmp-aa         (distillation: no matching lemma found)
    sizes: orig=15  classical=9  llm=37
    ABABAA   |     46 |     15 |     39 |    0.33  |    0.85   |   2.60
```

Three of four benchmarks: the LLM path matches or beats classical.

- **half-of-double** is the headline win: distillation chains
  `gHalf(gDouble(n)) = n` and `gEq(n, n) = True()` to reduce the input
  to a constant. **0 functions, 0 steps** — strictly smaller and
  faster than classical.
- **even-square** is the headline *size* win: same speed as classical
  (13 steps at n=12) but the residual is 4 functions vs. classical's
  328. Two-orders-of-magnitude smaller residual for identical
  runtime, via the single Lean-verified lemma
  `gEven(fSqr(x)) = gEven(x)`.
- **add-assoc** ties classical at 4 functions and 22 steps via the
  associativity lemma.
- **kmp-aa** still doesn't unlock — the input has only one call
  subexpression (`fMatch(...)`) and the LLM struggles to write a
  useful equation directly for `fMatch` rather than for the
  underlying `gN`/`gM` machinery.

**The harness is also a correctness check**: it verifies all three
variants produce the same value on every test input. Mismatches would
show as `*** VALUE MISMATCH ***` next to the row.

### What the numbers say

When distillation succeeds, the LLM path matches or *beats*
classical's performance with a strictly smaller residual. When the
LLM can't find or prove the right lemmas, the path falls back to
whistle-time generalizations and produces a compact, correct,
machine-checked residual — but with the same step count as the
original program.

Distillation succeeds on three of four benchmarks:

- `even-square`: LLM proposes `forall x, gEven(fSqr(x)) = gEven(x)`,
  Lean verifies; the rewriter applies it, the supercompiler drives
  `gEven(x)` to a 4-function residual. Same step count as classical
  (13 at n=12), 82x smaller code (classical's residual is 328
  functions). **Same speed, dramatically smaller.**
- `add-assoc`: LLM proposes `forall x y z, gAdd(gAdd(x,y),z) =
  gAdd(x, gAdd(y,z))`, Lean verifies; residual drops to 4 functions,
  matching classical at 22 steps for k=10.
- `half-of-double`: LLM chains two lemmas — `forall n,
  gHalf(gDouble(n)) = n` and `forall n, gEq(n, n) = True()`. The
  second proof failed on first attempt; the proof-retry loop fed the
  Lean error back and the LLM produced a working proof. Both lemmas
  apply, reducing the input to the constant `True()`. Residual: 0
  functions, 0 steps. **Strictly smaller than classical (2 functions,
  13 steps at n=12).**

Distillation doesn't succeed on `kmp-aa`: the input
`fMatch(Cons(A, Cons(A, Nil)), s)` has only one call subexpression
(`fMatch` itself), and the LLM struggles to write a useful equation
directly for `fMatch` rather than for the underlying `gN`/`gM`
machinery. The lemmas it proposes verify but don't pattern-match
the input.

The empirical answer to "is the LLM-augmented supercompiler better
than classical": **on three of four benchmarks, yes — either
strictly faster, or same-speed-but-much-smaller-code, or both**. On
the fourth, the LLM produces a correct residual that's bigger than
classical. This is exactly the regime the original PLAN.md was
aiming at: the LLM contributes semantic insight (parity-of-square,
gHalf-after-gDouble, associativity) that classical supercompilation
has no machinery to discover.

## Distillation pre-pass

Before driving starts, `supercompileIOWithTypes` runs a distillation
pre-pass (see `src/Distillation.hs` and the "Distillation" section of
`DESIGN_LEAN.md`):

1. Ask the LLM for a candidate lemma about the program + input
   expression. The lemma is `forall <vars>, lhs = rhs` plus a Lean
   proof body. Previously-verified lemmas in this run are listed in
   the prompt as available rewrite rules (`rw [lemma_n]` /
   `simp [lemma_n]`), so the LLM can decompose hard proofs into
   chains.
2. Render the lemma as a Lean theorem (via `embedLemma`) along with
   all previously-verified lemmas (re-stated with their original
   proofs) and verify via `LeanCheck.verify`. Lemmas usually need
   induction, so the LLM-supplied proof body is what gets checked —
   this is where the LLM-as-prover stage 2 finally does substantive
   work.
3. If verified, the lemma is added to the chain (passed forward to
   subsequent iterations) AND pattern-matched against subexpressions
   of the input (one-sided unifier; lemma's bound vars are
   metavariables). On a match, the input is rewritten to the lemma's
   RHS.
4. Repeat up to `maxDistillLemmas = 3` LLM calls per supercompile.

A typical successful trace:

```
[distill] requesting lemma #1 for: gEq(gHalf(gDouble(n)), n)
[distill] response: FORALL: n : Nat
LHS: gHalf(gDouble(n))
RHS: n
PROOF:
by induction n with | Z => rfl | S x ih => simp [gDouble, gHalf, gHalf1]; exact ih

[distill] parsed: gHalf(gDouble(n)) = n
[distill] lemma verified by Lean
[distill] applied: gEq(n, n)
[distill] driving rewritten task: gEq(n, n)
```

Failure modes (all graceful — fall through to driving the original
expression with whatever lemmas the chain accumulated):
- `lemma rejected: <lean error>` — Lean refused the proof
- `parse failed (or NONE)` — LLM declined or sent malformed output
- `lemma verified, kept in context (no match for e)` — proof was
  good but the LHS doesn't appear in the input expression. The
  lemma stays in the chain for subsequent iterations to use.

The proof step is non-deterministic: the same lemma target may
produce different proof attempts across runs (e.g. `simp` vs `simp
only`), with different outcomes. The system handles this with a
proof-retry loop: when Lean rejects an LLM-supplied proof, the
system reprompts the LLM with the failure output and asks for a
fixed proof of the *same* lemma (forall/lhs/rhs preserved, only the
`by …` body changes). Up to `distillProofRetries = 1` retry per
lemma. This is what enables the second lemma in the half-of-double
chain to verify on its second attempt.

## Benchmarks

| Name             | Input                                                 | Program  | Notes |
|------------------|-------------------------------------------------------|----------|-------|
| `even-square`    | `gEven(fSqr(x))`                                      | prog1    | The headline benchmark from PLAN.md. |
| `add-assoc`      | `gAdd(gAdd(x, y), z)`                                 | prog1    | Should drive into associativity-shaped residual. |
| `half-of-double` | `gEq(gHalf(gDouble(n)), n)`                           | prog3    | Property is identically `True`; supercompiler erases the equality. |
| `kmp-aa`         | `fMatch(Cons(A, Cons(A, Nil)), s)`                    | prog2    | KMP-style pattern matcher; uses `partial def` for `gM/gX/gN`. |

To add a benchmark, add an entry to `benchmarks` in `bench/Main.hs`.

## Known limitations

- **`supercompileIO` (the un-verified path) inherits the non-termination
  fix.** The `findFold` change in `bftIO` benefits both paths, so both
  now work on inputs that previously stack-overflowed.
- **The auto-prove tactic is a bare `simp_all` block.** It dispatches
  let-introductions (the common case) because let-elimination is a
  default simp rule. Anything requiring induction (e.g. `gAdd x Z ≡ x`)
  escalates to LLM-proof. We've yet to see a real benchmark hit that
  path with an Ok verdict; if a useful one shows up, we may widen with
  `first | simp_all | (intros; induction <;> simp_all)` before paying
  for an LLM proof call.
- **Name discipline at the LLM-supercompiler boundary.** The LLM may
  pick variable names that overlap with the supercompiler's pending
  fresh-name supply. Without care, this produces type-bogus expressions
  (a fresh Sym-typed pattern var ends up sharing a name with a
  pre-existing LSym-typed variable, etc.). `bftIO` filters
  LLM-introduced names out of the supply (`ns \\ vnames gen`) after
  every whistle-resolved generalization to keep names disjoint. (Same
  fragility used to crash the supercompiler with `head []` on a
  missing g-clause and a non-exhaustive `inject`; both patched in
  `Driving.hs`.)
- **Partial functions don't get equation lemmas in the simp set.** If
  you mark a function `funPartial`, the auto-prove can't unfold it via
  simp. This is fine for let-introductions (which don't need
  unfolding) but means more sophisticated proofs would need
  `f.eq_def`-style references via the LLM-as-prover.

## Reading a trace

Each whistle event is recorded as:

```
  [whistle] HE detected
    ancestor:  <...>
    current:   <...>
  [llm] call #<N>
  [llm] response: <raw LLM reply>
  [llm] parsed:   <SLL parsed form>
  [verify] auto-prove Ok       OR
  [verify] auto-prove Failed; asking LLM for proof
  [llm-proof] call #<N>
  [verify] LLM proof Ok        OR  LLM proof Failed: <stderr>
```

Inline fold events:

```
  [fold] back-edge to ancestor
    ancestor: <...>
    current:  <...>
```

Fallbacks:

```
  [whistle] budget exhausted, using classical
  [verify] LLM proof Failed: ... ; falling back to classical
```

## Cost notes

A typical run of all three benchmarks issues 10–15 Bedrock calls
(Sonnet 4.6, single-shot), runs in well under a minute, and creates a
short-lived per-run scratch directory under `$TMPDIR`. The scratch dir
is removed on success; on failure it's preserved (path printed in the
error) so the offending `Conjecture_<n>.lean` can be inspected.
