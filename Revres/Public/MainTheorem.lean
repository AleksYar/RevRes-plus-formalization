import Revres.Main
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Human-facing RevRes lower bound

This is the recommended Lean entry point for verifying the main theorem. It
provides transparent names, direct wrappers, and the elementary conversion from
the existing quantitative bounds to a size-based stretched exponential.
-/

namespace Revres.Public

/-- The explicit lifted cleaned Sink-of-DAG formula at family index `t`. -/
noncomputable def HardFormula (t : ℕ) :=
  Revres.indexLift (Revres.subsequenceBaseFormula t)

/-- Dense bit-size of `HardFormula t`, including variables, clause headers,
coefficient vectors, and right-hand-side bits. -/
noncomputable def FormulaBitSize (t : ℕ) : ℕ :=
  Revres.subsequenceFormulaSize t

/-- A RevRes refutation of `HardFormula t`. Its `length` is exactly the number
of recorded reversible local steps. -/
abbrev Refutation (t : ℕ) :=
  Revres.RevResRefutation (HardFormula t)

/-- The explicit real-valued lower-bound scale proved for every refutation. -/
noncomputable def LowerBound (t : ℕ) : ℝ :=
  Revres.subsequenceLengthScale t

/--
Paper correspondence: Main Theorem `thm:main` and Lemma `lem:lift-size` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

Mathematical content: The public finite construction is unsatisfiable, has
polynomially bounded dense bit-size, and forces every RevRes refutation above
the explicit quantitative lower scale.

Used by: This is the finite human-verification entry point for the hard family.
-/
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

private theorem formulaBitSize_nthRoot_le_degree (t : ℕ) :
    Nat.nthRoot 256 (FormulaBitSize t) ≤
      Revres.subsequenceDegree t := by
  rw [← Nat.lt_succ_iff, Nat.nthRoot_lt_iff (by norm_num)]
  exact (Revres.subsequenceFormulaSize_le t).trans_lt (by
    exact Nat.pow_lt_pow_left (by omega) (by norm_num))

/--
Paper correspondence: Main Theorem `thm:main` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

Mathematical content: Every RevRes refutation has an explicit pointwise
stretched-exponential lower bound in the dense bit-size of the hard formula.

Formalization note: Lean states the exact integer-power form using
`Nat.nthRoot 256` and natural division; it does not use `Real.exp`, a real root,
or asymptotic Omega notation.

Used by: This is the primary public manuscript-correspondence theorem.
-/
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

/-- For every fixed exponent `d`, sufficiently late formulas in the family
require more than the `d`-th power of their dense bit-size in RevRes steps. -/
theorem superpolynomial_lower_bound (d : ℕ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ∀ π : Refutation t,
        (FormulaBitSize t : ℝ) ^ d < (π.length : ℝ) := by
  simpa only [FormulaBitSize, Refutation, HardFormula] using
    Revres.subsequence_revres_superpolynomial_unconditional d

end Revres.Public
