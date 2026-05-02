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
translate `e` and `e'` into Lean and ask Lean (via `simp_all` over the
program's equation lemmas) to discharge the conjecture `⟦e⟧ = ⟦e'⟧`. If
Lean accepts, the LLM proposal is taken. If Lean rejects, we re-prompt
the LLM for a Lean proof body; if that also fails to verify, we fall
back to `classicalGeneralize` — the same strategy the pure path uses.

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
  }
```

`Demonstration.hs` carries `prog1Types`, `prog2Types`, `prog2aTypes`,
and `prog3Types`.

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

```
stack build && stack exec llm-bench
```

Expected output (numbers vary because the LLM is non-deterministic):

```
Running LLM-supercompiler benchmarks (real Bedrock calls).
Per-benchmark stderr traces under bench/results/

==> even-square
    residual: gg1(x)
    functions: 24 (expected 5-30)
    whistles: 8  folds: 6  llm: 8  auto-prove: 8 ok / 0 fail  budget: 0
    PASS
==> add-assoc
    residual: gg1(x, y, z)
    functions: 10 (expected 5-25)
    whistles: 2  folds: 3  llm: 2  auto-prove: 2 ok / 0 fail  budget: 0
    PASS
==> half-of-double
    residual: gg1(n)
    functions: 14 (expected 5-30)
    whistles: 2  folds: 3  llm: 2  auto-prove: 2 ok / 0 fail  budget: 0
    PASS

Summary: 3/3 passed.
```

Each benchmark passes if the supercompile terminates, the residual's
function count falls in the documented range, and **every** LLM proposal
verifies (`auto-prove ok == llm calls`, no fails, no max-whistles trip).

The full per-benchmark stderr trace is preserved at
`bench/results/<name>.trace` so you can inspect ancestor/current pairs,
LLM responses, and verification verdicts after the fact.

## Benchmarks

| Name             | Input                                      | Program  | Notes |
|------------------|--------------------------------------------|----------|-------|
| `even-square`    | `gEven(fSqr(x))`                           | prog1    | The headline benchmark from PLAN.md. |
| `add-assoc`      | `gAdd(gAdd(x, y), z)`                      | prog1    | Should drive into associativity-shaped residual. |
| `half-of-double` | `gEq(gHalf(gDouble(n)), n)`                | prog3    | Property is identically `True`; supercompiler erases the equality. |

To add a benchmark, add an entry to `benchmarks` in `bench/Main.hs`.

## Known limitations

- **KMP is not yet supported.** `prog2`'s mutually recursive `gM/gX/gN`
  pass `op` and `os` (the original pattern/string) unchanged through
  some calls; Lean's automatic structural-termination check can't see a
  decreasing measure. The embedding would need to emit
  `termination_by` clauses with a custom lex measure (length of `ss`
  paired with length of `pp`), which we don't synthesize automatically.
  Symptom: `lake build` fails inside `setupProject` with
  `fail to show termination for gX gN gM`.
- **`supercompileIO` (the un-verified path) inherits the non-termination
  fix.** The `findFold` change in `bftIO` benefits both paths, so both
  now work on inputs that previously stack-overflowed.
- **The auto-prove tactic is a single `simp_all [<all defs>]` block.**
  It dispatches let-introductions and any equivalence that's
  definitionally true after unfolding. Anything requiring induction
  (e.g. `gAdd x Z ≡ x`) escalates to LLM-proof. We've yet to see a real
  benchmark hit that path; if/when one does, we may want to widen the
  auto-prove tactic with `first | … | (induction <;> simp_all [defs])`
  before paying for an LLM proof call.

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
