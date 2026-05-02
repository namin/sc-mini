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

**With lemma chaining + proof retry** added on top, and after a
prompt-cleanup pass that removed a self-contradicting "propose
sub-lemmas this turn" instruction, distillation now matches or beats
classical on three of four benchmarks:

| Benchmark        | No distillation        | Distillation v3 (current)        |
|------------------|------------------------|----------------------------------|
| even-square      | 22 fns, n=12: 314 steps| **4 fns, 13 steps**              |
| add-assoc        | 8 fns, k=10: 32 steps  | 4 fns, 22 steps                  |
| half-of-double   | 14 fns, n=12: 64 steps | **0 fns, 0 steps**               |
| kmp-aa           | 37 fns                 | 37 fns (no help)                 |

For comparison classical's residuals are 328, 4, 2, and 9 functions
respectively. The LLM path is now smaller than classical on three of
four (only `kmp-aa` is bigger), and on `half-of-double` it's
strictly faster too.

The cleanest examples:

- **half-of-double**: LLM chains `gHalf(gDouble(n)) = n` and
  `gEq(n, n) = True()` (the second proof needed retry to succeed)
  to reduce the input to a constant. Zero residual functions, zero
  step count.
- **even-square**: LLM proposes `forall x, gEven(fSqr(x)) = gEven(x)`,
  Lean verifies, the rewriter applies it, supercompiler drives
  `gEven(x)` to 4 functions. *Same speed as classical, 82x smaller
  residual* (classical's brute-force unfolding hits 328 functions
  for the same 13-step output).

These are the kind of results classical can't reach: classical can't
know that "the parity of x squared equals the parity of x" or that
"halving twice the value gives the value back" — those are facts
about the equivalence relation, not the program structure. Only a
Lean-checked lemma puts them on the table.

**The remaining holdout, `kmp-aa`, is structurally different**: the
input `fMatch(Cons(A(), Cons(A(), Nil())), s)` has only one call
subexpression (`fMatch` itself), so there's nowhere to drill down.
The LLM keeps trying to write equations relating `gN`/`gM` to
`fMatch`, but those have wrong-side LHS (gN/gM, not fMatch) and
don't match the only candidate. Different problem from the other
three.

**The breakthrough was prompt simplification, not capability.** An
earlier prompt told the LLM "propose sub-lemmas this turn if you can't
prove the main one in one shot" — a permission that, in tension with
the implicit "your lemma must apply to the input" constraint,
encouraged the LLM to propose useful-but-non-applicable lemmas. With
that instruction removed and the constraint stated unambiguously, the
LLM started proposing on-target lemmas first try.

## How the pieces interact

For `half-of-double`, all three pieces (chaining, retry, clean
prompt) are necessary:

- Without retry: the second lemma (`gEq(n, n) = True()`) fails its
  first proof attempt and gets discarded; the chain never finishes.
- Without chaining: the working `gEq(n, n) = True()` proof would
  have nothing to reduce the input to `gEq(n, n)` first.
- Without the prompt cleanup: earlier runs with the
  decompose-into-sub-lemmas instruction had the LLM proposing
  off-target lemmas instead of `gHalf(gDouble(n)) = n` directly, and
  the chain never started.

Budget-wise: 3 proposals × 2 attempts per proposal = 6 Bedrock calls
max per supercompile. In practice half-of-double used 5 (2 clean
first-tries + 1 retry), which is modest given the result.

`kmp-aa` remains the holdout. Its input has one call subexpression
(`fMatch(...)`) and no useful equation directly *for* `fMatch` is
something the LLM is willing to propose — it keeps trying equations
relating `gN`/`gM` to `fMatch`, with the wrong side as LHS. Likely
fixes:
- Make the rewriter accept LHS = subexpression *modulo program
  unfolding* (so a lemma about `gM(p, s, p, s)` would apply to
  `fMatch(p, s)` after unfolding `fMatch(p, s) = gM(p, s, p, s)`).
  This is real engineering on the rewriter, not prompt work.
- Or switch to a less reductionist test input where there are more
  candidate subexpressions.

**Not yet:**
1. **Smarter rewriter — pattern match modulo program unfolding**:
   currently a lemma's LHS must syntactically match a subexpression.
   Allow it to match after one or two steps of f-call unfolding (and
   maybe g-call dispatch with a known constructor). Would unlock
   `kmp-aa` and broaden the class of useful lemmas in general.
2. **Try every lemma in the chain against the input on each
   iteration**: currently we only try the most recently verified
   lemma against the current expression. A re-application pass would
   pick up cases where an earlier off-target lemma becomes
   on-target after the input shape changes.
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
