import Revres.LowerBound.Parameters
import Revres.SoPL.HardnessProof

/-!
# Subsequence lower bound

This file packages the explicit lifted Sink-of-DAG family. The conditional
lower-bound API is retained, and the proved support-local SoPL hardness theorem
supplies its unconditional instantiation.
-/

namespace Revres

open Filter

/-- The support-local path-family hardness required uniformly along the fixed
subsequence. -/
def SubsequencePathFamilyHardness : Prop :=
  ∀ t : ℕ,
    SoPL.PathFamilyNSHardness
      (subsequenceEll t)
      (subsequenceEll_pos t)
      (subsequenceHardnessDegree t)

/-- The support-local path-family hardness holds uniformly along the fixed
subsequence. -/
theorem subsequencePathFamilyHardness :
    SubsequencePathFamilyHardness := by
  intro t
  exact SoPL.pathFamilyNSHardness_of_size
    (subsequenceEll_pos t)
    (subsequence_hardness_size_condition t)

/-- Every ordinary formula underlying the explicit family is unsatisfiable. -/
theorem subsequenceBaseFormula_unsat (t : ℕ) :
    (subsequenceBaseFormula t).Unsat := by
  simpa [subsequenceBaseFormula, SoD.Preprocess.cleaningFormula] using
    SoD.Encoding.searchCNF_unsat
      (2 * subsequenceEll t)
      (SoD.ActiveEdge.ambientWidth_pos (subsequenceEll_pos t))

/-- Truth-table lifting preserves unsatisfiability for every family member. -/
theorem subsequenceFormula_unsat (t : ℕ) :
    RevresUnsat (indexLift (subsequenceBaseFormula t)) :=
  indexLift_unsat (subsequenceBaseFormula_unsat t)

/-- Exact conditional lower bound along the explicit subsequence. -/
theorem subsequence_revres_lower_bound
    (hHard : SubsequencePathFamilyHardness)
    (t : ℕ)
    (π : RevResRefutation (indexLift (subsequenceBaseFormula t))) :
    subsequenceLengthScale t ≤ (π.length : ℝ) := by
  apply (subsequenceLengthScale_le_finiteScale t).trans
  simpa [subsequenceBaseFormula] using
    finite_revres_lower_bound
      (subsequenceEll_pos t)
      (subsequence_localOrder_gt_one t)
      (hHard t)
      (subsequence_transferDegree t)
      (subsequence_smallDegree t)
      π

/-- Exact unconditional lower bound along the explicit subsequence. -/
theorem subsequence_revres_lower_bound_unconditional
    (t : ℕ)
    (π : RevResRefutation (indexLift (subsequenceBaseFormula t))) :
    subsequenceLengthScale t ≤ (π.length : ℝ) :=
  subsequence_revres_lower_bound subsequencePathFamilyHardness t π

/-- Every fixed power of the concrete dense formula size is eventually below
the length of every RevRes refutation, conditional only on path-family
hardness. -/
theorem subsequence_revres_superpolynomial
    (hHard : SubsequencePathFamilyHardness)
    (d : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      ∀ π : RevResRefutation (indexLift (subsequenceBaseFormula t)),
        (subsequenceFormulaSize t : ℝ) ^ d < (π.length : ℝ) := by
  let K := decompositionDecayDenominator * (256 * d + 9)
  have hgrowth :
      ∀ᶠ t : ℕ in atTop,
        K * subsequenceShift t < 2 ^ subsequenceShift t := by
    simpa [K, subsequenceShift] using
      (Filter.tendsto_add_atTop_nat 16).eventually (eventually_linear_lt_two_pow K)
  filter_upwards [hgrowth] with t ht
  intro π
  calc
    (subsequenceFormulaSize t : ℝ) ^ d ≤
        (2 : ℝ) ^ (256 * d * subsequenceShift t) :=
      formula_power_le_degree_exponent t d
    _ < subsequenceLengthScale t := by
      exact degree_exponent_lt_lengthScale d t (by simpa [K] using ht)
    _ ≤ (π.length : ℝ) := subsequence_revres_lower_bound hHard t π

/-- Every fixed power of the concrete dense formula size is eventually below
the length of every RevRes refutation, without an external hardness
hypothesis. -/
theorem subsequence_revres_superpolynomial_unconditional
    (d : ℕ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ∀ π : RevResRefutation (indexLift (subsequenceBaseFormula t)),
        (subsequenceFormulaSize t : ℝ) ^ d < (π.length : ℝ) :=
  subsequence_revres_superpolynomial subsequencePathFamilyHardness d

end Revres
