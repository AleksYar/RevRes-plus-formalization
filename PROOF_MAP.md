# Mathematical Proof Map

This is the major mathematical dependency spine of the RevRes lower bound. It is
not an import graph and intentionally omits bookkeeping and implementation
lemmas. Manuscript labels below refer to
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

## Capstone View

```text
Revres.Public.hard_family_properties
├── explicit hard formula is unsatisfiable
├── its dense bit-size is polynomially bounded
└── every refutation satisfies the finite lower scale

Revres.Public.stretched_exponential_lower_bound
├── dense size bound gives nthRoot 256 size <= degree
└── finite lower scale gives the pointwise integer-power bound

Revres.Public.superpolynomial_lower_bound
└── the finite lower scale eventually beats every fixed power of dense bit-size
```

## Proof Spine

### 1. Explicit Family, Unsatisfiability, And Dense Size

Manuscript correspondence: Lemma `lem:lift-size`, equation `eq:polysize`.

The cleaned Sink-of-DAG search CNF is truth-table lifted to the final parity CNF;
the lift preserves unsatisfiability, and the actual dense encoding is bounded by
an explicit polynomial.

- `Revres.subsequenceFormula_unsat` in `Revres/Main.lean`
- `Revres.subsequenceFormulaSize_le` in `Revres/LowerBound/Parameters.lean`

### 2. RevRes Conservation And Endpoint Identity

Manuscript correspondence: Section `sec:revres`, Lemma
`lem:strong-soundness`, and Proposition `prop:static` with equation `eq:static`.

Every reversible rule preserves the number of falsified clauses at each Boolean
assignment, yielding a static identity between the initial and final blackboards.

- `Revres.static_endpoint_identity` in `Revres/RevRes/Endpoint.lean`

### 3. Affine-To-Conical Decomposition

Manuscript correspondence: Section `sec:indexing-lift`, Lemma
`lem:affine-conical`, equations `eq:decomp` and `eq:error`.

Every affine gadget-fiber density decomposes into a bounded-degree nonnegative
conical junta plus a uniformly small nonnegative error.

- `Lemma53.Lemma53` in `Lemma53/Lemma53.lean`

### 4. Robust Identity Extraction

Manuscript correspondence: Section `sec:short-to-robust`, equations
`eq:master`, `eq:Jbound`, and `eq:Ebound`.

Endpoint conservation, truth-table averaging, and the affine decomposition turn
a short RevRes refutation into an exact robust identity with an error controlled
by the refutation length.

- `Revres.revres_to_robust_identity` in `Revres/LowerBound/RobustIdentity.lean`

### 5. Preprocessing And Certificate Transfer

Manuscript correspondence: Lemma `lem:cleaning` and Lemma
`lem:stage-restriction` with equation `eq:stage-restriction`.

The conical junta is node-aligned, made exit-curious, and stripped of witnessing
terms. Generic bounded-depth decision-tree formulations transfer semantic
Nullstellensatz certificates with an explicit degree cost.

- `Revres.SoD.Preprocess.preprocess` in `Revres/SoD/Preprocess/Main.lean`
- `Revres.certificate_transfer` in `Revres/DecisionTree/Transfer.lean`
- `Revres.SoD.Amplification.restricted_certificate` in
  `Revres/SoD/Amplification/Growth.lean`

`certificate_transfer` is the generic transfer engine. The concrete
paper-facing stage statement is `restricted_certificate`, where the active-edge
formulation and preprocessing layer supply the problem-specific data.

### 6. Robust Sink-Of-DAG Amplification

Manuscript correspondence: Lemma `lem:one-step-amplification` and Lemma
`lem:robust-sod` with equations `eq:robust-id` and `eq:Jlarge`.

One internal macrogrid stage multiplies the certified junta lower bound by at
least `7/5`; iteration reaches the final macro-row with exponential growth.

- `Revres.SoD.Amplification.amplification_step` in
  `Revres/SoD/Amplification/Step.lean`
- `Revres.SoD.Amplification.exists_last_amplification_state` in
  `Revres/SoD/Amplification/Iterate.lean`
- `Revres.sod_cleaningFormula_robustAmplification` in
  `Revres/LowerBound/Finite.lean`

The paper's one-step factor is `4/3`; the formal capstone proves the stronger
explicit factor `7/5`. The direct Lean counterpart of `lem:robust-sod` is
`sod_cleaningFormula_robustAmplification`.

### 7. Support-Local SoPL Hardness

Manuscript correspondence: Theorem `thm:sopl` and Corollary
`cor:sopl-path`.

A low-degree certificate on encoded path families would yield a low-degree OR
approximator. The explicit approximate-degree bound gives a quadratic certificate
degree lower bound and a finite-size hardness bridge.

- `Revres.SoPL.pathFamilyNS_degree_quadratic` in
  `Revres/SoPL/HardnessProof.lean`
- `Revres.SoPL.pathFamilyNSHardness_of_size` in
  `Revres/SoPL/HardnessProof.lean`

SoPL is an internal hardness ingredient. The final hard formula remains the
lifted cleaned Sink-of-DAG formula from Node 1. Although the manuscript presents
`thm:sopl` as an external input, this formalization proves the explicit
support-local bound internally.

### 8. Finite Lower-Bound Dichotomy

Manuscript correspondence: Section `sec:main-proof`, equations `eq:case1` and
`eq:case2`.

If the decomposition error is large, the refutation is already long; if it is
small, robust amplification forces a large junta value and hence a long
refutation.

- `Revres.finite_revres_lower_bound` in `Revres/LowerBound/Finite.lean`

### 9. Uniform Subsequence Parameters And Hardness

Manuscript correspondence: Section `sec:main-proof`, equation
`eq:degree-choice`.

The fixed subsequence simultaneously satisfies the transfer-degree, small-degree,
and SoPL hardness-size inequalities, removing all caller-supplied side conditions.

- `Revres.subsequence_hardness_size_condition` in
  `Revres/LowerBound/Parameters.lean`
- `Revres.subsequencePathFamilyHardness` in `Revres/Main.lean`

### 10. Size-Based And Asymptotic Conversion

Manuscript correspondence: Main Theorem `thm:main`, Lemma `lem:lift-size`, and
equation `eq:nlower`.

The dense size is at most `subsequenceDegree t ^ 256`, while the finite lower
scale is exponential in a positive linear fraction of `subsequenceDegree t`.
Taking the integer `256`th root of the size inequality and using monotonicity of
natural division and powers of two gives the pointwise public bound

```text
(1 / 200) * 2 ^
  (Nat.nthRoot 256 (FormulaBitSize t) /
    decompositionDecayDenominator)
<= π.length.
```

The two direct inputs to this conversion are:

- `Revres.subsequenceFormulaSize_le` in
  `Revres/LowerBound/Parameters.lean`
- `Revres.subsequence_revres_lower_bound_unconditional` in `Revres/Main.lean`

The reader-facing endpoint is
`Revres.Public.stretched_exponential_lower_bound`. Separately, fixed-base
exponential growth proves that every fixed power of dense size is eventually
below every refutation length:

- `Revres.subsequence_revres_superpolynomial_unconditional` in `Revres/Main.lean`

`Revres.Public.superpolynomial_lower_bound` is the transparent reader-facing
wrapper around that eventual conversion.

## Core Mathematical Checkpoints

| Checkpoint | Manuscript location | Capstone declaration | Source file | What a reviewer checks |
|---|---|---|---|---|
| Reversible semantics | `lem:strong-soundness`, `prop:static` | `Revres.derivation_conservation`, `Revres.static_endpoint_identity_indexed` | `Revres/RevRes/Conservation.lean`, `Revres/RevRes/Endpoint.lean` | One-step conservation iterates to the manuscript's pointwise endpoint identity |
| Affine decomposition | `lem:affine-conical` | `Lemma53.Lemma53` | `Lemma53/Lemma53.lean` | The conical part is nonnegative and low-degree, and the error is exponentially small |
| Robust identity | `sec:short-to-robust` | `Revres.revres_to_robust_identity` | `Revres/LowerBound/RobustIdentity.lean` | A refutation produces the exact identity and a step-count-controlled error |
| Certificate transfer | `lem:cleaning`, `lem:stage-restriction` | `Revres.SoD.Preprocess.preprocess`, `Revres.SoD.Amplification.restricted_certificate` | `Revres/SoD/Preprocess/Main.lean`, `Revres/SoD/Amplification/Growth.lean` | The cleaned certificate transfers to the current SoPL stage with the stated degree cost |
| Amplification | `lem:one-step-amplification`, `lem:robust-sod` | `Revres.SoD.Amplification.amplification_step`, `Revres.sod_cleaningFormula_robustAmplification` | `Revres/SoD/Amplification/Step.lean`, `Revres/LowerBound/Finite.lean` | The `7/5` formal one-step growth iterates to the robust amplification property |
| SoPL hardness | `thm:sopl`, `cor:sopl-path` | `Revres.SoPL.pathFamilyNS_degree_quadratic`, `Revres.SoPL.pathFamilyNSHardness_of_size` | `Revres/SoPL/HardnessProof.lean` | The internally proved quadratic bound discharges the manuscript hardness input |
| Finite lower bound | `eq:case1`, `eq:case2` | `Revres.finite_revres_lower_bound` | `Revres/LowerBound/Finite.lean` | Both error cases force the stated refutation-length scale |
| Explicit family | `lem:lift-size` | `Revres.Public.hard_family_properties` | `Revres/Public/MainTheorem.lean` | Unsatisfiability, dense size, and finite lower bound are bundled without assumptions |
| Stretched-exponential capstone | `thm:main` | `Revres.Public.stretched_exponential_lower_bound` | `Revres/Public/MainTheorem.lean` | The dense-size and finite lower bounds imply the pointwise integer-root estimate |
| Asymptotic capstone | `thm:main` | `Revres.Public.superpolynomial_lower_bound` | `Revres/Public/MainTheorem.lean` | Every fixed polynomial in dense bit-size is eventually beaten |

For the exact mathematical/Lean dictionary, see
[`THEOREM_GUIDE.md`](THEOREM_GUIDE.md). The reader-facing Lean statements are in
[`Revres/Public/MainTheorem.lean`](Revres/Public/MainTheorem.lean).
