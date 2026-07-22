# Verifying the RevRes Lower Bound

This guide answers one question: how can a reader check that the Lean theorem is
the claimed lower bound?

## Start Here

- Public Lean theorem: [`Revres/Public/MainTheorem.lean`](Revres/Public/MainTheorem.lean)
- Mechanical trust audit: [`Revres/Public/Audit.lean`](Revres/Public/Audit.lean)
- Mathematical dependency map: [`PROOF_MAP.md`](PROOF_MAP.md)
- Main manuscript: [`revres_xor_superpoly_lower_bound_restriction_notation.tex`](revres_xor_superpoly_lower_bound_restriction_notation.tex)

`MainTheorem.lean` contains transparent names and elementary wrappers only. The
mathematical implementation remains in `Revres/` and the stable affine
decomposition library `Lemma53/`.

## Mathematical Statement

For each `t ∈ ℕ`, put

```text
s_t := t + 16
A_t := 2 ^ s_t
Ψ_t := Revres.Public.HardFormula t
S_t := Revres.Public.FormulaBitSize t
D   := Revres.decompositionDecayDenominator
L_t := Revres.Public.LowerBound t
```

Here `Ψ_t` is the truth-table index lift of a cleaned Sink-of-DAG CNF. Lean
proves:

1. `Ψ_t` is unsatisfiable for every `t`;
2. `S_t ≤ A_t ^ 256`;
3. every `π : Revres.Public.Refutation t` satisfies `L_t ≤ π.length`;
4. every such `π` satisfies the pointwise stretched-exponential bound

   ```text
   (1 / 200) * 2 ^ ((Nat.nthRoot 256 S_t) / D) ≤ π.length;
   ```

5. for every fixed `d ∈ ℕ`, all sufficiently large `t` satisfy
   `S_t ^ d < π.length` for every such refutation `π`.

The original finite lower scale is

```text
L_t = (1 / 200) * 2 ^ (A_t / D).
```

The size inequality gives `Nat.nthRoot 256 S_t ≤ A_t`, so monotonicity of
natural division and powers of two places the displayed size-based bound below
`L_t`. This is exactly the short mathematical conversion performed by
`stretched_exponential_lower_bound`.

Both operations in the size-based exponent are natural-number operations. If
`q_t := Nat.nthRoot 256 S_t`, then

```text
q_t ^ 256 ≤ S_t < (q_t + 1) ^ 256,
```

and `q_t / D` is floor division by the fixed positive integer `D`. Consequently,
as `S_t` grows,

```text
q_t / D = S_t ^ (1 / 256) / D + O(1),
2 ^ (q_t / D) = exp(Ω(S_t ^ (1 / 256))).
```

This is the manuscript's stretched-exponential form with an explicit exponent
`1/256`, up to fixed constants and the two floor operations. The Lean theorem
itself states the integer-power inequality; it does not contain real roots,
`Real.exp`, `O`, or `Ω` notation.

In the asymptotic Lean theorem, `∀ᶠ t : ℕ in Filter.atTop` means that there is an
index `t₀` such that the statement holds for every `t ≥ t₀`.

## Exact Lean Statements

The primary manuscript-correspondence theorem in `Revres.Public` is:

```lean
theorem stretched_exponential_lower_bound
    (t : ℕ) (π : Refutation t) :
    (1 / 200 : ℝ) *
        (2 : ℝ) ^
          (Nat.nthRoot 256 (FormulaBitSize t) /
            Revres.decompositionDecayDenominator) ≤
      (π.length : ℝ) := by
  apply le_trans ?_ (Revres.subsequence_revres_lower_bound_unconditional t π)
  unfold Revres.subsequenceLengthScale
  have hquotient :
      Nat.nthRoot 256 (FormulaBitSize t) /
          Revres.decompositionDecayDenominator ≤
        Revres.subsequenceDegree t /
          Revres.decompositionDecayDenominator :=
    Nat.div_le_div_right (formulaBitSize_nthRoot_le_degree t)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num) hquotient) (by norm_num)
```

The finite construction theorem is:

```lean
theorem hard_family_properties (t : ℕ) :
    RevresUnsat (HardFormula t) ∧
    FormulaBitSize t ≤ Revres.subsequenceDegree t ^ 256 ∧
    ∀ π : Refutation t,
      LowerBound t ≤ (π.length : ℝ) := by
  exact ⟨
    Revres.subsequenceFormula_unsat t,
    Revres.subsequenceFormulaSize_le t,
    Revres.subsequence_revres_lower_bound_unconditional t
  ⟩
```

The separate eventual corollary is:

```lean
theorem superpolynomial_lower_bound (d : ℕ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ∀ π : Refutation t,
        (FormulaBitSize t : ℝ) ^ d < (π.length : ℝ) := by
  simpa only [FormulaBitSize, Refutation, HardFormula] using
    Revres.subsequence_revres_superpolynomial_unconditional d
```

## Line-By-Line Dictionary

| Mathematics | Lean | Exact meaning |
|---|---|---|
| Hard formula `Ψ_t` | `Revres.Public.HardFormula t` | Truth-table index lift of the cleaned Sink-of-DAG CNF at index `t` |
| Formula size `S_t` | `Revres.Public.FormulaBitSize t` | Dense encoding size including variables, clause headers, coefficient vectors, and right-hand-side bits |
| RevRes refutation | `Revres.Public.Refutation t` | Explicit reversible derivation whose initial clauses are supported by the formula, whose initial board has no empty clause, and whose final board contains one |
| Proof length | `π.length` | Exact number of recorded reversible local steps |
| Finite lower scale `L_t` | `Revres.Public.LowerBound t` | `(1 / 200) * 2 ^ (A_t / D)` as a real number with a natural exponent |
| Size-based exponent | `Nat.nthRoot 256 S_t / D` | Integer `256`th root followed by natural floor division |
| Unsatisfiable | `RevresUnsat (HardFormula t)` | Every Boolean assignment falsifies a clause of the lifted formula |

## Critical Definitions

### Refutation Object

The proof object is the following six-field structure.

```lean
structure RevResRefutation (G : Finset (ParityClause X)) where
  initial : Blackboard X
  final : Blackboard X
  derivation : RevDerivation initial final
  initial_supported : ∀ B ∈ initial, B ∈ G
  initial_empty_free : ([] : ParityClause X) ∉ initial
  final_has_empty : ([] : ParityClause X) ∈ final
```

Thus a refutation records an initial multiset, a final multiset, and every
reversible local step between them. Its initial board may repeat or omit clauses
of `G`, but every occurrence must come from `G`; no non-axiom clause is allowed.
For empty-free `G`, the board containing each clause exactly once is one special
case. The public theorem therefore covers the larger class of all supported
initial multisets, not only that standard initial board.

### Proof Length

```lean
def length : ℕ :=
  π.derivation.length
```

This is exactly the number of recorded reversible local steps. It is not the
number of clauses at an endpoint, a tree size, a compressed line count, or the
bit length of a serialized proof.

### Dense Formula Bit-Size

```lean
noncomputable def indexLiftBitSize {N : ℕ} (F : CNF N) : ℕ :=
  3 * N + (indexLift F).card +
    ∑ D ∈ indexLift F, D.length * (3 * N + 1)
```

The three summands count:

1. the `3 * N` Boolean variables;
2. one header or delimiter for every lifted parity clause;
3. a dense `3 * N`-bit coefficient vector and one right-hand-side bit for every
   parity-equation occurrence.

This is the declared public dense encoding measure, rather than clause count,
variable count, or the sum of clause widths alone.

### Explicit Hard Family

```lean
noncomputable def subsequenceBaseFormula (t : ℕ) :
    CNF (SoD.Encoding.variableCount (2 * subsequenceEll t)) :=
  SoD.Preprocess.cleaningFormula (subsequenceEll_pos t)
```

In mathematical shorthand,

```text
subsequenceBaseFormula t
  = padded-ambient cleaned Sink-of-DAG search CNF;
HardFormula t
  = indexLift (subsequenceBaseFormula t).
```

The pointer width is `2 * subsequenceEll t`. SoPL path-family hardness is an
internal ingredient in the amplification argument; the final public formula
family is the lifted cleaned Sink-of-DAG family, not an SoPL formula family.

## Five Facts To Check

| Fact | Source | Mathematical content | Direct major dependency |
|---|---|---|---|
| `Revres.subsequenceFormula_unsat` | [`Revres/Main.lean`](Revres/Main.lean) | Every lifted hard instance is semantically unsatisfiable | `subsequenceBaseFormula_unsat` and `indexLift_unsat` |
| `Revres.subsequenceFormulaSize_le` | [`Revres/LowerBound/Parameters.lean`](Revres/LowerBound/Parameters.lean) | The actual dense bit-size is at most `subsequenceDegree t ^ 256` | Explicit search-CNF and truth-table-lift size estimates in the same file |
| `Revres.subsequence_revres_lower_bound_unconditional` | [`Revres/Main.lean`](Revres/Main.lean) | Every refutation has length at least `subsequenceLengthScale t` | The conditional finite-family theorem instantiated by `subsequencePathFamilyHardness` |
| `Revres.Public.stretched_exponential_lower_bound` | [`Revres/Public/MainTheorem.lean`](Revres/Public/MainTheorem.lean) | Every refutation satisfies the pointwise integer-root lower bound in dense bit-size | `subsequenceFormulaSize_le` and `subsequence_revres_lower_bound_unconditional` |
| `Revres.Public.superpolynomial_lower_bound` | [`Revres/Public/MainTheorem.lean`](Revres/Public/MainTheorem.lean) | Every fixed polynomial in dense bit-size is eventually beaten | `subsequence_revres_superpolynomial_unconditional` |

`Revres.Public.hard_family_properties` simply bundles the first three facts. The
stretched-exponential theorem combines Facts 2 and 3 through the private
integer-root comparison. For the mathematical path below these capstones, see
[`PROOF_MAP.md`](PROOF_MAP.md).

## Trust Audit

Run both checks:

```bash
bash scripts/check_lean_placeholders.sh
lake env lean Revres/Public/Audit.lean
```

The shell scan rejects unreviewed whole-word `sorry`, `admit`, or `axiom`
occurrences throughout `Revres/**/*.lean` and `Lemma53/**/*.lean`; its five
allowlisted hits are prose-only and introduce no Lean declaration. The Lean
audit checks all three public theorems, including
`stretched_exponential_lower_bound`, and their compiled dependency footprint.
The same source scan runs before compilation in
`.github/workflows/lean_action_ci.yml`. The audit output contains only:

```text
propext
Classical.choice
Quot.sound
```

These are standard Lean/Mathlib foundational principles. No project-specific
hardness assumption, `sorry`, or custom axiom occurs in the public theorem chain.

## Scope Caveats

- The formulas form an explicit dependent sequence because their variable types
  grow with `t`.
- The theorem concerns the dense measure `FormulaBitSize` and the reversible-step
  count `π.length`.
- The compiled stretched-exponential statement uses an integer root and a
  natural power. Its real-root and `exp(Ω(...))` form is the elementary
  mathematical interpretation above, not additional Lean syntax.
- The construction is stated on the fixed explicit subsequence; it does not
  claim the same bound for every possible pointer width.
