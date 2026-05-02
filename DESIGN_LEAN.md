# SLL → Lean Embedding: Design

The supercompiler proposes a generalization `e ≡ e'` mid-drive. We need
Lean to mechanically check that proposal. This doc fixes the embedding
scheme; the LLM prompt and the Haskell-side wiring are downstream.

## Two-stage verification

The LLM is responsible only for proposing `e'` (in SLL — it must feed
back into the supercompiler as the next configuration). The proof is
a separate concern, attempted by the supercompiler in two stages:

1. **Auto-prove.** One canned tactic, one `lean` call. The tactic is
   roughly `by intros; simp_all [<every f-def, every g-clause>]` —
   `simp_all` with the program's equation lemmas as a rewrite set.
   This dispatches `Let`-introductions and any generalization that's
   definitionally true after unfolding, which we expect to cover the
   common case.
2. **LLM-as-prover.** Only if the auto-prove fails: prompt the LLM
   with the conjecture and the failure stderr, asking for a `by …`
   block. ≤ N retries with stderr fed back. Fall through to classical
   generalization on persistent failure.

Logging which stage succeeds gives a free measurement of when the LLM
is actually contributing on the proof side vs. just the proposal side.

The auto-prove tactic might grow over time (e.g. wrapping in
`first | … | (induction …; simp_all [defs])` once we see what fails),
but it stays a single Lean tactic block, not a Haskell-driven ladder.

## Project layout

Each supercompile run gets its own scratch directory (a tempdir, or
`./.work/<runId>/`). The `proofs/` lake project is materialized inside
that directory at the start of the run, so:

- two supercompiles running side by side don't clash on `proofs/`;
- build artifacts stay out of the repo;
- inspection of failed proofs is easy (the dir persists until cleanup).

The program's defs are compiled to a `.olean` *once* per run; each
verification re-elaborates only its own conjecture file, which
`import`s the cached defs.

```
<runDir>/
  proofs/
    lakefile.toml       -- minimal: one library "Program"
    lean-toolchain      -- pins lean to 4.29.1 (matches ~/.elan)
    Program.lean        -- generated from (Program, TypeEnv); inductives + defs
    Conjecture_<n>.lean -- one per verification call; .gitignored regardless
```

Conjectures use a per-call counter `<n>` rather than a single shared
filename: surviving files are useful for post-mortem debugging, and
unique filenames keep the door open to concurrent verifications later
(`Program.olean` is built once and read-only, so parallel
`lake env lean` invocations against different conjecture files are
fine).

`Program.lean` shape:

```lean
-- one inductive per DataDef in the TypeEnv
inductive Nat' where | Z : Nat' | S : Nat' → Nat'
inductive Bool' where | True : Bool' | False : Bool'
...

-- f's and g's, mutual block when needed
mutual
  def gEven : Nat' → Bool' | .Z => .True | .S x => gOdd x
  def gOdd  : Nat' → Bool' | .Z => .False | .S x => gEven x
end
def fSqr (x : Nat') : Nat' := gMult x x
...
```

`Conjecture.lean` shape:

```lean
import Program

theorem gen_ok : ∀ x, gEven (fSqr x) = <e'> := by
  <auto-prove tactic, or LLM-supplied proof on fallback>
```

## Run loop

1. **Supercompile start.** Create `<runDir>/proofs/`. Emit
   `Program.lean` from the current `(Program, TypeEnv)`, plus the
   fixed `lakefile.toml` and `lean-toolchain`. Run `lake build` once.
   ~1-2s; pays for itself after the first verification.
2. **Per verification.** Allocate a fresh counter `n`. Write
   `Conjecture_<n>.lean`. Run `lake env lean
   proofs/Conjecture_<n>.lean` from `<runDir>`. Capture exit code
   and stderr.
3. **Verdicts.** Exit 0 → ok. Anything else → fail; failure modes
   (parse error, type error, `sorry`, unsolved goals) all collapse
   to "fail" with stderr attached. On auto-prove failure we escalate
   to the LLM; on LLM-proof failure we feed stderr back and retry.

## Type information

SLL is monomorphic but untyped on the page. Rather than infer types
at embedding time (a bail-out hazard whenever a program is
syntactically irregular), we carry a hand-written `TypeEnv` next to
each `Program`. `Types.hs` defines:

```haskell
data Type    = TyCon Name
data CtrDef  = CtrDef Name [Type]
data DataDef = DataDef Name [CtrDef]
data TypeEnv = TypeEnv
  { typeDefs   :: [DataDef]
  , funSigs    :: [(Name, Signature)]
  , funPartial :: [Name]
  }
```

Each demo program has a sibling `progNTypes :: TypeEnv` (see
`Demonstration.hs`). Every Lean inductive comes from a `DataDef`;
every Lean function signature comes from `funSigs`; every constructor's
field types are read out of its `DataDef`. No inference, no bail-out.

The `funPartial` field lists function names to emit as `partial def`
rather than `def`. Use it for functions whose termination Lean can't
prove automatically (KMP's `gM/gX/gN`, where `gN` restarts from the
original pattern so there's no structurally decreasing measure).
Partial defs don't get equation lemmas in the simp set, but our
auto-prove relies on let-elimination — not function unfolding — so
`partial def` is verification-compatible for typical let-introduction
conjectures. To make `partial def` work, every emitted inductive
gets `deriving Inhabited` unconditionally; SLL types always have at
least one nullary constructor, so deriving succeeds automatically.

This means SLL programs that aren't well-typed under any monomorphic
assignment simply don't get a `TypeEnv` written for them, and the
embedder won't run on them. That's a feature: the trust boundary is
"the user wrote a `TypeEnv` consistent with the program," not "our
inferencer agreed with the user's intent."

Future work, if it pays off: extend the parser/quasi-quoter to accept
inline `data Nat = Z | S(Nat);` and `gAdd : Nat -> Nat -> Nat;`
declarations and synthesize the `TypeEnv` automatically. The
`Types.hs` types stay the same; only the front-end changes.

## Name mapping

SLL identifiers are Lean-legal as-is. Concretely:

- Constructors → constructors of their Lean inductive (`Nat'.Z`, etc.).
  Type names get a trailing prime to avoid clashes with Lean's `Nat`,
  `Bool`, `List`.
- f-functions and g-functions keep their SLL names verbatim (`gAdd`,
  `fSqr`). Lean is fine with leading-lowercase `g` / `f`.
- Variables keep their SLL names. SLL `vnames` are simple alphas;
  no clashes with Lean keywords expected, but we'll add a small
  reserved-word escape (`type`, `fun`, `match`, ...) if it bites.

## Function translation

| SLL                          | Lean |
|------------------------------|------|
| `FDef f [a,b] body`          | `def f (a : T₁) (b : T₂) : T := ⟦body⟧` |
| `GDef g (Pat C vs) ys body`  | one match arm `\| .C vs … ys => ⟦body⟧` (multiple `GDef`s for same `g` collapse into one `def g … := match arg₀ with …`) |
| `Var n`                      | `n` |
| `Ctr C es`                   | `.C ⟦e₁⟧ … ⟦eₙ⟧` (anonymous constructor, type inferred) |
| `FCall f es`                 | `f ⟦e₁⟧ … ⟦eₙ⟧` |
| `GCall g es`                 | `g ⟦e₁⟧ … ⟦eₙ⟧` |
| `Let (v,e₁) e₂`              | `let v := ⟦e₁⟧; ⟦e₂⟧` |

g-functions: collapse the `[GDef]` list per name into a single
`def` whose body is `match arg₀ with …`. The remaining args are
named once at the def head and reused in every arm.

**Totality.** Each g-function's scrutinee type comes from `funSigs`,
and the constructors of that type come from `typeDefs`. A well-formed
SLL program covers every constructor in its clauses, so the `match`
is exhaustive. For most programs that's enough and Lean accepts the
function as `def`. For programs whose recursion isn't structurally
decreasing (KMP-style: gN restarts the pattern, so the measure is
lex over (string-position, pattern-position)), Lean's automatic
termination check fails. We don't synthesize `termination_by` clauses;
instead the user opts those functions into `funPartial` and we emit
`partial def`. Partial defs don't get equation lemmas in the simp
set, but our auto-prove uses bare `simp_all` (let-elimination only),
so they verify cleanly for the let-introduction conjecture shapes
the supercompiler emits in practice.

**Mutual recursion.** Compute the call-graph SCCs over `[FDef] ∪ [GDef]`
and emit each non-trivial SCC inside a single `mutual … end` block.
Trivial SCCs (singletons with no self-loop) emit as plain `def`. Order
SCCs in reverse topological order so each block's dependencies are
already in scope.

## The conjecture

The whistle fires with ancestor `a` and current `e`. The LLM proposes
`e'` (typically a `Let`-introduction). We need:

```lean
theorem gen_ok : ∀ <fv₁ : T₁> … <fvₙ : Tₙ>, ⟦e⟧ = ⟦e'⟧ := by
  <proof>
```

where `<fvᵢ : Tᵢ>` are the free variables of `e` ∪ `e'`. Each variable's
type is determined by its use site against the `TypeEnv`: first arg of
a g-function, n-th arg of an f-function, n-th field of a constructor.

If a free variable's type can't be uniquely determined from use sites
in `e ∪ e'`, we treat the conjecture as ill-formed and fall back. (In
practice every whistle-target is a call, so each free var has at least
one typing constraint.)

## Distillation

The perf harness (`bench/Perf.hs`) showed that the LLM's
let-introduction proposals preserve operation count: the residual is
*compact and correct*, but not faster than the original. To beat
classical (which gets up to 24x speedups by aggressive unfolding) the
LLM needs to propose **eureka lemmas** — equalities like
`forall n, gHalf(gDouble(n)) = n` that change which expressions are
*equivalent*, not just how they're structured. Validation (manually
distilling `half-of-double` with one Lean-verified lemma) gave a 5x
speedup with a 7x smaller residual; this section covers the design of
turning that into an automated pipeline.

### Lemma data model

```haskell
data Lemma = Lemma
  { lemmaName    :: Name           -- printable, e.g. "lemma_1"
  , lemmaForall  :: [(Name, Type)] -- universally-quantified vars + types
  , lemmaLhs     :: Expr           -- pattern: SLL expression with lemmaForall vars free
  , lemmaRhs     :: Expr           -- replacement, same free vars
  , lemmaProof   :: String         -- Lean `by …` block
  }
```

Both `lemmaLhs` and `lemmaRhs` are SLL expressions: lemmas live in the
SLL world and rewriting produces SLL, so the supercompiler can drive
the rewritten configuration normally afterward. The proof is Lean.

### Where lemmas fire: pre-pass

The validation experiment ran the rewrite *before* the supercompiler
started driving — and that was already enough to close the gap to
classical. v1 keeps that shape: distillation is a pre-pass on the
input task, not woven into `bftIO`.

```
supercompileIOWithTypes env (e, p):
   ┌───────────────────────────────────────────────┐
   │ distillation pre-pass                         │
   │   for i in 1..N:                              │
   │     lemma <- proposeLemma env p e_i           │
   │     if verifyLemma env p lemma == Ok:         │
   │       e_{i+1} <- rewrite lemma e_i            │
   │     else: stop                                │
   └───────────────┬───────────────────────────────┘
                   ↓
              bftIO on e_N
```

The pre-pass shape keeps distillation fully decoupled from the
supercompiler's drive/whistle/fold mechanics. Intra-supercompile
triggering (e.g. "ask for a lemma when HE fires repeatedly without
making progress") is more sophisticated but has more knobs and more
ways to mis-fire — defer until/unless we see a benchmark that needs it.

### Prompt strategy

Broad rather than targeted: "given this program and this expression,
propose an equation that simplifies it." The LLM is told the lemma
must be (a) universally quantified over typed variables, (b) have an
SLL LHS that pattern-matches a subexpression of the input, (c) have
an RHS that's also SLL, and (d) come with a Lean proof.

A targeted variant ("propose a lemma whose LHS rewrites *this exact
subexpression*") would be cleaner but assumes we know which
subexpression to focus on. v1 leaves that to the LLM.

### Pattern matching

Lemma application is *unification* (one-sided: lemma LHS is a pattern
with `lemmaForall` variables; the candidate is a closed subexpression
of the input). This is **not** `msg`/anti-unification — we want
"does the candidate match the pattern" with a substitution, not the
common generalization of two terms.

Algorithm: walk the input top-down; at each subexpression `s`, try to
unify `lemmaLhs ~ s` treating `lemmaForall` names as metavariables.
If unification succeeds with substitution σ, replace `s` with
`lemmaRhs[σ]`. Recurse on children otherwise.

### Fixed-point iteration

After each successful lemma application, the rewritten expression is
the new "input" — and the LLM may now spot another lemma that helps.
Iterate up to a budget (e.g. 3 lemmas) or until the LLM declines to
propose more.

### Verification

Same pipeline as generalization conjectures: render the lemma to a
`Conjecture_<n>.lean` file, run `lake env lean`, accept on exit 0.
The crucial difference: lemmas usually need induction, so bare
`simp_all` won't discharge them — the LLM-supplied proof body is
what gets verified. Stage 2 of the two-stage strategy finally does
substantive work.

When chaining is active, all previously-verified lemmas are inlined
above the new theorem in the Conjecture file (with their checked
proofs). Lean accepts them, then they're available to the new proof
as `rw [lemma_n]` / `simp [lemma_n]` rules.

If the LLM's proof fails to verify, the system reprompts the LLM
with the Lean error and asks for a fixed proof of the *same* lemma
(forall/lhs/rhs preserved, only the `by …` body changes). Up to
`distillProofRetries = 1` retry per lemma. The retry prompt is
distinct from the proposal prompt — it specifies the lemma to prove
and the prior failure verbatim, plus a small set of common-fixes
hints (e.g. "prefer `simp` over `simp only`", "use `Nat'.S` not
`S`"). Empirically the retry is what unlocks chained proofs that
the LLM can't get right on the first attempt.

### What v1 doesn't do

- No persistent lemma library across supercompile runs.
- No targeted ("lemma about this subexpression") prompting.
- No lemma *chaining* (using a verified lemma as a hypothesis when
  proving a subsequent one). Each lemma proves against the program's
  base equations only.
- No intra-supercompile triggering (mid-`bftIO` lemma proposal).
- No automatic detection of "did distillation actually help" —
  benchmarks measure step counts post-hoc, but the supercompiler
  doesn't decide whether to keep a lemma based on residual quality.

## Module layout

Four new Haskell modules:

- `LeanEmbed.hs` — pure rendering.
  - `embedProgram    :: TypeEnv -> Program -> String`
  - `embedExpr       :: TypeEnv -> Expr -> String`
  - `embedConjecture :: TypeEnv -> Program -> Expr -> Expr -> String -> String`
    last `String` is the proof body (auto-tactic or LLM-supplied);
    returns the full `Conjecture.lean` source (with `import Program`).
  - `embedLemma      :: TypeEnv -> Program -> Lemma -> String`
    renders a `Lemma` as a `Conjecture.lean` file with the LLM's
    `by …` block.
- `LeanCheck.hs` — IO oracle. Owns one `<runDir>/proofs/` per run.
  - `data LeanProject` — opaque handle: run dir, conjecture counter.
  - `data Verdict = Ok | Failed { stderr :: String }`
  - `setupProject :: TypeEnv -> Program -> IO LeanProject`
    creates the run dir and `proofs/` scaffold, writes `Program.lean`,
    runs `lake build`. Called once per supercompile.
  - `verify :: LeanProject -> String {- conjecture lean source -} -> IO Verdict`
    allocates a fresh counter, writes `Conjecture_<n>.lean`, runs
    `lake env lean`, captures stderr.
  - `teardownProject :: LeanProject -> IO ()` — optional, removes the
    run dir on success.
- `LeanProver.hs` — the two-stage strategy.
  - `autoTactic   :: TypeEnv -> Program -> String` — emits the canned
    `by intros; simp_all` block.
  - `tryAuto      :: TypeEnv -> Program -> Expr -> Expr -> IO Bool` —
    runs `LeanCheck.verify` with the auto tactic.
- `Distillation.hs` — lemma proposal, verification, rewriting.
  - `data Lemma` (above).
  - `proposeLemma   :: TypeEnv -> Program -> Expr -> IO (Maybe Lemma)`
    asks Bedrock for a candidate lemma, parses the response.
  - `verifyLemma    :: TypeEnv -> Program -> Lemma -> LeanProject -> IO Bool`
    renders + checks via `LeanCheck.verify`.
  - `rewrite        :: Lemma -> Expr -> Maybe Expr`
    pattern-matches `lemmaLhs` against subexpressions of the input;
    returns `Just` rewritten expression on first match, `Nothing` if
    the lemma doesn't apply anywhere.
  - `distillTask    :: TypeEnv -> Program -> Expr -> LeanProject -> IO Expr`
    runs the pre-pass: propose, verify, rewrite, repeat ≤ N times.

Flow in `LLMSupercompiler.supercompileIOWithTypes`:

```
setupProject env p
  → distillTask env p e proj    (pre-pass: rewrites e using verified lemmas)
  → bftIO with verified-whistle on e'
       (per whistle:
         LLM proposes e''
         tryAuto
           ↳ Ok    → accept
           ↳ Fail  → LLM proves; verify; on fail → classicalGeneralize)
  → residuate ∘ simplify ∘ foldTree
```

## What v1 deliberately doesn't do

- No real polymorphism — every type is monomorphic, declared per program.
- No partial functions, no `Option`-wrapping. If totality fails, bail.
- No tactic library beyond the canned auto-prove block. If it proves
  too narrow in practice we'll widen it (more `simp` lemmas, an
  `induction` branch via `first | …`), but it stays one tactic.
- No concurrent verifications used in v1. The supercompiler is
  sequential by nature (one whistle, one generalization). The design
  doesn't preclude concurrency — per-call conjecture filenames mean
  parallel `lake env lean` invocations are safe — but we're not
  driving any from the Haskell side yet.
- No caching of (e, e') verdicts across calls. Add later if it matters.
