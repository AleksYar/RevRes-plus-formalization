# RevRes over Parities: Lean Formalization

This repository formalizes a lower-bound argument for reversible resolution over
parities, written `RevRes(+)` in the project directory and `RevRes(oplus)` in the
accompanying manuscript. The development connects an explicit RevRes refutation to
an affine-to-conical decomposition, semantic Nullstellensatz certificates,
decision-tree transfer, and a robust Sink-of-DAG amplification argument.

The formalization currently proves a **conditional superpolynomial lower bound**
for an explicit infinite subsequence of lifted, unsatisfiable Sink-of-DAG formulas.
The only remaining mathematical hypothesis is the support-local approximate
Nullstellensatz hardness of Sink-of-Potential-Line (SoPL). That result is represented
by an explicit Lean proposition; it is not introduced as an axiom.

## Status

There are two Lean libraries in the package:

| Library | Status | Entry point |
|---|---|---|
| `Lemma53` | Complete and unconditional | `Lemma53/Lemma53.lean` |
| `Revres` | Complete conditional on SoPL path-family hardness | `Revres/Main.lean` |

The source files contain no `sorry`, `admit`, or project-specific axioms. Axiom
audits of the capstone declarations report only:

```text
propext
Classical.choice
Quot.sound
```

These are the standard logical principles used by Lean and Mathlib in this
development.

The exact remaining boundary is:

```lean
def Revres.SubsequencePathFamilyHardness : Prop := ...
```

Every final lower-bound theorem receives a proof of this proposition as an explicit
argument. See [Remaining Work](#remaining-work) for the work needed to remove it.

## Formalized Result

For `t : Nat`, the explicit subsequence uses

```text
s_t                  = t + 6
ell_t                = 8 * s_t
degree_t             = 2 ^ s_t
hardnessDegree_t     = 2 ^ (4 * s_t)
```

The ordinary base CNF is the canonical cleaned Sink-of-DAG search formula at
pointer width `2 * ell_t`:

```lean
Revres.subsequenceBaseFormula t
```

The corresponding parity CNF is its constant-size truth-table index lift:

```lean
Revres.indexLift (Revres.subsequenceBaseFormula t)
```

Every member of this lifted family is semantically unsatisfiable, without using the
hardness hypothesis:

```lean
theorem Revres.subsequenceFormula_unsat (t : Nat) :
    RevresUnsat (indexLift (subsequenceBaseFormula t))
```

The natural-power lower scale is

```text
(1 / 200) * 2 ^ (degree_t / decompositionDecayDenominator).
```

The exact conditional family theorem is:

```lean
theorem Revres.subsequence_revres_lower_bound
    (hHard : SubsequencePathFamilyHardness)
    (t : Nat)
    (pi : RevResRefutation (indexLift (subsequenceBaseFormula t))) :
    subsequenceLengthScale t <= (pi.length : Real)
```

The concrete dense formula-size measure satisfies

```lean
theorem Revres.subsequenceFormulaSize_le (t : Nat) :
    subsequenceFormulaSize t <= subsequenceDegree t ^ 256
```

and the capstone theorem states that every fixed polynomial in this size is
eventually smaller than every RevRes refutation length:

```lean
theorem Revres.subsequence_revres_superpolynomial
    (hHard : SubsequencePathFamilyHardness)
    (d : Nat) :
    Filter.Eventually
      (fun t => forall pi : RevResRefutation
          (indexLift (subsequenceBaseFormula t)),
        (subsequenceFormulaSize t : Real) ^ d < (pi.length : Real))
      Filter.atTop
```

The formulas at different indices have different variable types. The family is
therefore expressed as a dependent sequence rather than forced into one homogeneous
`Set`.

## Size Conventions

### Formula size

The project does not identify formula size with only the number of clauses or only
the number of variables. For an ordinary CNF `F : CNF N`, it defines

```lean
noncomputable def Revres.indexLiftBitSize (F : CNF N) : Nat :=
  3 * N +
    (indexLift F).card +
      Finset.sum (indexLift F)
        (fun D => D.length * (3 * N + 1))
```

This dense encoding counts:

1. the `3 * N` Boolean variables of the indexing gadget;
2. one delimiter or header unit per parity clause; and
3. a dense `3 * N` coefficient vector plus one right-hand-side bit for every
   parity-equation occurrence.

The polynomial size proof follows the actual search-CNF construction through
verifier leaves. It does not use the exponentially larger set of all possible
clauses.

### Refutation length

`RevResRefutation.length` is the number of recorded reversible derivation steps.
The capstone lower bound concerns this exact measure. It is not a separate bit
encoding of proof lines.

## Mathematical Architecture

The proof is organized into the following stages.

### 1. Reversible resolution semantics

Parity equations and clauses are interpreted by their falsifying affine spaces.
RevRes blackboards are multisets, so clause multiplicity is preserved. Each local
reversible rule preserves the pointwise number of falsified clauses. Chaining the
rules gives the static endpoint identity.

### 2. Endpoint cancellation and truth-table lifting

Canonical multiset subtraction removes common initial and final occurrences. The
remaining endpoint has size at most twice the derivation length. Ordinary clauses
are lifted through the `3`-bit indexing gadget and converted to parity clauses.

### 3. Affine-to-conical decomposition

The unconditional theorem `Lemma53.Lemma53` decomposes every gadget-fiber density
of an affine subspace as

```text
density = conical junta + nonnegative error,
```

where the conical junta has bounded degree and the error decays exponentially in
that degree. Exact averaging of lifted clause indicators transfers the RevRes
endpoint identity into a robust polynomial identity.

### 4. Polynomial certificates and decision-tree transfer

Ordinary clauses receive multilinear Boolean clause polynomials. Semantic
Nullstellensatz certificates are normalized without increasing degree. Generic
decision trees are represented by bounded-degree multilinear polynomials and
transfer certificates between canonical search CNFs with an explicit degree cost.

### 5. SoPL and Sink-of-DAG encodings

The project formalizes the combinatorial semantics first and then their binary
encodings. Canonical search clauses are generated by reachable accepting leaves of
bounded-depth output verifiers. Exact binary pointer codes use order `2 ^ ell - 1`,
with the all-zero word representing `none`.

### 6. Junta preprocessing

The conical junta is transformed into a form suitable for amplification:

- node alignment completes every partially read node record;
- exit curiosity completes designated successor records; and
- witnessing terms are removed through an explicit bounded-degree certificate.

The cleaned junta stays nonnegative, has controlled degree, and is pointwise
dominated by the original junta.

### 7. Robust macrogrid amplification

Sink-of-Potential-Line is embedded into successive boxes of a larger Sink-of-DAG
instance. A good amplification state records its restriction, current box, stage,
and numerical lower bound. Each step uses support-local SoPL hardness, rewiring,
cleanup averaging, and a structural update to multiply the lower bound by `7 / 5`.
Iteration reaches the last macro-row.

### 8. Finite dichotomy and asymptotics

The finite theorem combines two cases:

- the decomposition error is large, directly forcing a long refutation; or
- the error is small, allowing robust amplification to force a large conical-junta
  value and hence a long refutation.

The fixed subsequence discharges all finite degree side conditions. A natural power
of two lies below both branches of the finite minimum. The actual lifted formula
has polynomial dense encoding size, and fixed-base exponential growth then yields
the eventual superpolynomial theorem.

## Repository Layout

### Stable affine decomposition library

```text
Lemma53/
  Gadget.lean         3-bit indexing gadget and fibers
  LinearAlgebra.lean  finite-dimensional linear algebra over F_2
  Selector.lean       selector constructions
  GoodBad.lean        good/bad decomposition
  LemmaA.lean         the auxiliary high-rank estimate
  MainLemma.lean      parameterized affine-to-conical theorem
  Lemma53.lean        unconditional capstone theorem
```

`Lemma53/` is treated as a complete, frozen library. New lower-bound work belongs
under `Revres/`.

### RevRes and lifting layers

```text
Revres/RevRes/        parity clauses, blackboards, rules, conservation, refutations
Revres/CNF/           ordinary clauses and finite CNFs
Revres/Lift/          truth-table lifting and exact gadget-fiber averaging
Revres/Conical/       canonical terms, completions, and explicit conical juntas
```

### Certificate and transfer infrastructure

```text
Revres/Polynomial/    clause polynomials and semantic NS certificates
Revres/DecisionTree/  Boolean decision trees, search CNFs, and certificate transfer
Revres/Encoding/      exact binary pointer encoding
Revres/Grid/          square-grid combinatorics
```

### Search problems and amplification

```text
Revres/SoPL/                 SoPL semantics, path families, encoding, hardness interface
Revres/SoD/                  Sink-of-DAG semantics, encoding, and macrogrid geometry
Revres/SoD/Preprocess/       node alignment, curiosity, and witness removal
Revres/SoD/Amplification/    states, growth, rewiring, cleanup, steps, and iteration
```

### Lower bounds and entry points

```text
Revres/LowerBound/RobustIdentity.lean
Revres/LowerBound/AmplificationProperty.lean
Revres/LowerBound/Abstract.lean
Revres/LowerBound/Finite.lean
Revres/LowerBound/Parameters.lean
Revres/Main.lean
Revres.lean
```

`Revres.lean` is the umbrella import for the completed development.

## Important Declarations

| Declaration | Purpose |
|---|---|
| `Lemma53.Lemma53` | Unconditional affine-to-conical decomposition |
| `Revres.derivation_conservation` | Pointwise conservation along a RevRes derivation |
| `Revres.static_endpoint_identity` | Static identity between residual endpoints |
| `Revres.indexLift_unsat` | Truth-table lifting preserves unsatisfiability |
| `Revres.revres_to_robust_identity` | Robust identity extracted from a refutation |
| `Revres.certificate_transfer` | Decision-tree transfer of NS certificates |
| `Revres.SoPL.PathFamilyNSHardness` | Explicit external hardness proposition |
| `Revres.SoD.Preprocess.preprocess` | Complete cleaned-junta preprocessing |
| `Revres.SoD.Amplification.amplification_step` | One robust amplification step |
| `Revres.SoD.Amplification.exists_last_amplification_state` | Iterated amplification capstone |
| `Revres.finite_revres_lower_bound` | Exact conditional finite lower bound |
| `Revres.subsequenceFormulaSize_le` | Explicit polynomial formula-size bound |
| `Revres.subsequence_revres_lower_bound` | Exact conditional subsequence bound |
| `Revres.subsequence_revres_superpolynomial` | Conditional family-size capstone |

For the complete API inventory and implementation decisions, see `PROGRESS.md`.

## Building the Project

### Prerequisites

- [Elan](https://github.com/leanprover/elan), the Lean toolchain manager;
- the Lean version pinned by `lean-toolchain`; and
- network access on first setup to obtain Mathlib or its build cache.

The repository currently pins:

```text
Lean     4.32.0
Mathlib  v4.32.0
```

After cloning, fetch the Mathlib cache and build the full RevRes library:

```bash
lake exe cache get
lake build Revres
```

The package name and default target remain `lemma53`. Consequently:

```bash
lake build
```

checks the default `Lemma53` library, while:

```bash
lake build Revres
```

checks the complete RevRes development and its dependencies.

### Fast checks during development

Check one source file directly:

```bash
lake env lean Revres/LowerBound/Parameters.lean
lake env lean Revres/Main.lean
```

If an imported source file changed, rebuild that module before checking downstream
files so Lean does not read a stale `.olean`:

```bash
lake build Revres.Lift.Formula
lake build Revres.LowerBound.Parameters
lake build Revres.Main
```

Useful final checks are:

```bash
lake build
lake build Revres
rg -n -P '^\s*(sorry|admit|axiom)\b|(:=|=>|\bby)\s+(sorry|admit)\b|^import Mathlib$' \
  Revres Lemma53
```

The repository intentionally avoids the umbrella `import Mathlib`; modules use
targeted Mathlib imports.

## Axiom Auditing

To inspect the trusted footprint of the main declarations, create a temporary Lean
file containing:

```lean
import Revres.Main

#print axioms Revres.subsequence_transferDegree
#print axioms Revres.subsequenceLengthScale_le_finiteScale
#print axioms Revres.subsequenceFormulaSize_le
#print axioms Revres.subsequence_revres_lower_bound
#print axioms Revres.subsequence_revres_superpolynomial
```

Then run it with:

```bash
lake env lean /path/to/AxiomAudit.lean
```

The expected output for every declaration is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Source Documents

The repository includes the mathematical and engineering sources used by the
formalization:

| File | Role |
|---|---|
| `revres_xor_superpoly_lower_bound_restriction_notation.tex` | Main mathematical manuscript |
| `RevRes_Lean_Formalization_Roadmap.md` | Formalization architecture and milestones |
| `PROGRESS.md` | Completed milestones, APIs, decisions, and verification record |
| `CURRENT_TASK.md` | Current scoped implementation task |
| `CURRENT_TASK_*.md` | Archived tasks for completed phases |
| `Lemma53.txt` | Mathematical source for the affine-to-conical lemma |
| `Lemma52.txt` | Source of the auxiliary lemma used by `Lemma53` |
| `AGENTS.md` | Repository-specific instructions for coding agents |

When source prose and Lean disagree about an implemented API, the compiled Lean
declarations are authoritative.

## Remaining Work

### External support-local SoPL hardness

The internal RevRes proof is complete conditional on
`Revres.SoPL.PathFamilyNSHardness`. A self-contained, unconditional main theorem
still requires a Lean proof of the uniform proposition

```lean
Revres.SubsequencePathFamilyHardness
```

The planned PR 28+ work includes:

1. the randomized reduction from `OR` to canonical encoded SoPL instances;
2. proof that the reduction's support lies in the formalized path family;
3. the planted-sink and local-indistinguishability calculation;
4. conversion of an approximate NS certificate into a low-degree `OR`
   approximator; and
5. the approximate-degree lower bound for `OR` with explicit finite constants.

This is a separate major formalization project, not a missing local lemma.

### Parameter threshold before the external proof

The current conditional interface asks for degree at least

```text
2 ^ (4 * s), where ell = 8 * s.
```

Since the corresponding SoPL order is `2 ^ (8 * s) - 1`, this is essentially a
square-root degree bound. The manuscript's stated reduction loses a logarithmic
factor and directly yields only a bound of the form `c * sqrt(n) / log n`, later
weakened to `n ^ a` for some `a > 0`.

Therefore, formalizing the published argument will also require one of the
following:

- lower `subsequenceHardnessDegree` to a conservative exponent and increase the
  fixed shift enough to absorb all explicit constants and finite exceptions; or
- strengthen the external reduction to remove the logarithmic degree loss.

The first option leaves the decomposition, dense formula-size estimate, and
asymptotic mechanism intact. Only the hardness threshold and its finite arithmetic
need to be adjusted.

### Optional quantitative packaging

The exact lower scale and the `degree ^ 256` formula-size bound already imply a
stretched-exponential lower bound mathematically. The current Lean capstone exposes
the cleaner consequence that every fixed polynomial is eventually beaten. A final
unconditional project may also package explicit constants in a theorem matching the
manuscript's `exp(c * L ^ epsilon)` statement.

## Development Rules

- Keep `Lemma53/` stable; add adapters and new proof layers under `Revres/`.
- Reuse `Lemma53.F2` rather than defining another copy of the field.
- Do not add `sorry`, `admit`, hidden assumptions, or a hardness axiom.
- Keep exact finite inequalities until the final asymptotic layer.
- Use narrow Mathlib imports.
- Read `CURRENT_TASK.md` and `PROGRESS.md` before changing proof code.
- Update `PROGRESS.md` when a milestone or established design decision changes.

See `AGENTS.md` for the complete repository workflow and scope rules.
