# RevRes over Parities: Lean Formalization

This repository formalizes a lower bound for reversible resolution over parities,
written `RevRes(+)` here and `RevRes(oplus)` in the manuscript. The completed Lean
theorem is unconditional.

## What Is Formally Proved?

For each `t : ℕ`, let

```text
Ψ_t := Revres.Public.HardFormula t
S_t := Revres.Public.FormulaBitSize t
D   := Revres.decompositionDecayDenominator.
```

`Ψ_t` is the truth-table lift of an explicit cleaned Sink-of-DAG CNF, `S_t` is
its dense bit-size, and `D` is a fixed positive natural number. The primary
manuscript-style public theorem is the following pointwise bound for every
family index and every RevRes refutation:

```lean
namespace Revres.Public

theorem stretched_exponential_lower_bound
    (t : ℕ) (π : Refutation t) :
    (1 / 200 : ℝ) *
        (2 : ℝ) ^
          (Nat.nthRoot 256 (FormulaBitSize t) /
            Revres.decompositionDecayDenominator) ≤
      (π.length : ℝ)

end Revres.Public
```

Here `Nat.nthRoot` is the floor-style integer root, and division by `D` is
natural-number floor division. Thus the exact Lean lower bound is

```text
(1 / 200) * 2 ^ ((Nat.nthRoot 256 S_t) / D).
```

As `S_t` grows, the two floor operations change the exponent only by fixed
multiplicative and additive constants. Together with
`2^x = exp((log 2) * x)`, this is the integer-power form of
`exp(Ω(S_t^(1/256)))` from the manuscript. Lean states the displayed
integer-power inequality exactly; it does not encode the `Ω` notation.

The companion finite theorem proves that every `Ψ_t` is unsatisfiable, that
`S_t ≤ subsequenceDegree t ^ 256`, and that every refutation has at least the
original explicit lower scale `LowerBound t` recorded reversible steps. The
separate asymptotic corollary proves that every fixed polynomial in `S_t` is
eventually beaten.

```lean
namespace Revres.Public

theorem hard_family_properties (t : ℕ) :
    RevresUnsat (HardFormula t) ∧
    FormulaBitSize t ≤ Revres.subsequenceDegree t ^ 256 ∧
    ∀ π : Refutation t,
      LowerBound t ≤ (π.length : ℝ)

theorem superpolynomial_lower_bound (d : ℕ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ∀ π : Refutation t,
        (FormulaBitSize t : ℝ) ^ d < (π.length : ℝ)

end Revres.Public
```

The formulas have growing variable types, so Lean represents them as an explicit
dependent sequence rather than one homogeneous `Set`.

### Manuscript Correspondence

| Manuscript statement | Public Lean declaration |
|---|---|
| Explicit unsatisfiable polynomial-size family | `Revres.Public.hard_family_properties` |
| Stretched-exponential lower bound in ordinary bit-size | `Revres.Public.stretched_exponential_lower_bound` |
| Consequent superpolynomial lower bound | `Revres.Public.superpolynomial_lower_bound` |

The second row uses an exact natural-power formulation rather than real roots,
`Real.exp`, or asymptotic notation.

## Start Verification

- Lean entry point: [`Revres/Public/MainTheorem.lean`](Revres/Public/MainTheorem.lean)
- Theorem dictionary: [`THEOREM_GUIDE.md`](THEOREM_GUIDE.md)
- Mathematical dependency map: [`PROOF_MAP.md`](PROOF_MAP.md)
- Trust and axiom audit: [`Revres/Public/Audit.lean`](Revres/Public/Audit.lean)

Run the audit with:

```bash
lake env lean Revres/Public/Audit.lean
```

It reports only `propext`, `Classical.choice`, and `Quot.sound`, the standard
Lean/Mathlib principles used by this development. The source contains no `sorry`,
`admit`, project-specific axiom, or caller-supplied hardness hypothesis in the
public theorem.

## Status And Parameters

| Library | Status | Reader-facing entry point |
|---|---|---|
| `Lemma53` | Complete and unconditional | `Lemma53/Lemma53.lean` |
| `Revres` | Complete and unconditional | `Revres/Public/MainTheorem.lean` |

The explicit subsequence uses

```text
s_t                  = t + 16
ell_t                = 8 * s_t
degree_t             = 2 ^ s_t
hardnessDegree_t     = 2 ^ (3 * s_t)
```

and the finite lower scale is

```text
L_t = (1 / 200) * 2 ^
  (degree_t / decompositionDecayDenominator).
```

SoPL hardness, with explicit constant `C_sopl = 8192`, is proved internally and
used by amplification. The final hard formula itself is lifted cleaned Sink-of-DAG,
not an SoPL formula.

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

### 8. Support-local SoPL hardness

The support-local certificate reduction constructs an ordinary polynomial
approximator for `OR` with degree at most sixteen times the certificate degree.
Boolean multilinearization, slice symmetrization, and an explicit integer-grid
Markov inequality prove the required quadratic approximate-degree lower bound.
The resulting bridge has the fixed constant `C_sopl = 8192` and turns a strict
binary-pointer size inequality into `PathFamilyNSHardness`.

### 9. Finite dichotomy and quantitative conversion

The finite theorem combines two cases:

- the decomposition error is large, directly forcing a long refutation; or
- the error is small, allowing robust amplification to force a large conical-junta
  value and hence a long refutation.

The fixed subsequence discharges all finite degree side conditions and the SoPL
hardness-size premise. A natural power of two lies below both branches of the
finite minimum. The actual lifted formula has polynomial dense encoding size.
Taking its integer `256`th root gives a pointwise stretched-exponential lower
bound in that size, while fixed-base exponential growth separately yields the
unconditional eventual superpolynomial theorem.

## Repository Layout

### Public verification layer

```text
Revres/Public/MainTheorem.lean  transparent vocabulary and headline theorems
Revres/Public/Audit.lean        mechanical API and trust audit
THEOREM_GUIDE.md                exact mathematical/Lean dictionary
PROOF_MAP.md                    major mathematical dependency spine
```

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
Revres/ApproxDegree/  multilinearization, symmetrization, and OR degree bounds
```

### Search problems and amplification

```text
Revres/SoPL/                 SoPL semantics, encoding, approximate NS, and hardness proof
Revres/SoPL/ApproxNS/        support-local reduction from path certificates to OR
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
| `Revres.SoPL.pathFamilyNS_degree_quadratic` | Support-local quadratic certificate-degree bound |
| `Revres.SoPL.pathFamilyNSHardness_of_size` | Finite-size bridge to path-family hardness |
| `Revres.SoD.Preprocess.preprocess` | Complete cleaned-junta preprocessing |
| `Revres.SoD.Amplification.amplification_step` | One robust amplification step |
| `Revres.SoD.Amplification.exists_last_amplification_state` | Iterated amplification capstone |
| `Revres.finite_revres_lower_bound` | Exact conditional finite lower bound |
| `Revres.subsequenceFormulaSize_le` | Explicit polynomial formula-size bound |
| `Revres.subsequence_hardness_size_condition` | Uniform parameter inequality for the hardness bridge |
| `Revres.subsequencePathFamilyHardness` | Proved uniform SoPL hardness on the subsequence |
| `Revres.subsequence_revres_lower_bound_unconditional` | Exact unconditional subsequence bound |
| `Revres.subsequence_revres_superpolynomial_unconditional` | Unconditional family-size capstone |
| `Revres.Public.hard_family_properties` | Human-facing finite family theorem |
| `Revres.Public.stretched_exponential_lower_bound` | Human-facing pointwise stretched-exponential capstone |
| `Revres.Public.superpolynomial_lower_bound` | Human-facing unconditional asymptotic capstone |

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

The repository includes a mechanical audit of the public declarations and their
unconditional implementation dependencies. Run:

```bash
lake env lean Revres/Public/Audit.lean
```

The expected trusted footprint for every printed theorem is:

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
| `Nex_Roadmap_ADAPTED.md` | Adapted roadmap through the unconditional capstone |
| `HUMAN_READABILITY_REFACTOR_PLAN.md` | Plan for the human-facing verification API |
| `THEOREM_GUIDE.md` | Exact mathematical statement, Lean dictionary, and five-fact audit |
| `PROOF_MAP.md` | Major mathematical dependency spine |
| `PROGRESS.md` | Completed milestones, APIs, decisions, and verification record |
| `CURRENT_TASK.md` | Current scoped implementation task |
| `CURRENT_TASK_*.md` | Archived tasks for completed phases |
| `Lemma53.txt` | Mathematical source for the affine-to-conical lemma |
| `Lemma52.txt` | Source of the auxiliary lemma used by `Lemma53` |
| `AGENTS.md` | Repository-specific instructions for coding agents |

When source prose and Lean disagree about an implemented API, the compiled Lean
declarations are authoritative.

## Current Boundary

The adapted roadmap through PR 40 is complete. The SoPL hardness theorem, the
uniform subsequence arithmetic, and the finite, stretched-exponential, and
asymptotic RevRes lower bounds are all proved declarations. The public capstones
have no custom mathematical hypothesis.

The result is stated along the explicit dependent subsequence above. It does not
claim a homogeneous formula family with one fixed variable type or a lower bound
for every possible pointer width.

The stretched-exponential theorem is compiled in the exact integer-root form
shown above. The formal statement does not use a real `256`th root, `Real.exp`,
or `Ω`; their relation to the integer-power statement is the elementary
mathematical interpretation recorded in `THEOREM_GUIDE.md`. Paper/source labels
on the internal proof spine remain future readability work.
