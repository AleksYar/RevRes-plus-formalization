import Revres.LowerBound.AmplificationProperty
import Mathlib.Tactic.Linarith

/-!
# Conditional RevRes lower bound

The completed robust identity implies an exact finite lower bound from any proof of the abstract
robust amplification property.  The minimum in the final statement records the small-error and
large-error regimes without asymptotic notation.
-/

namespace Revres

variable {N : ℕ}

/-- The robust identity with its conical junta converted to an explicit finitely supported
representation. -/
theorem revres_to_explicit_robust_identity
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    (degree : ℕ) :
    ∃ (P E : (Fin N → Lemma53.F2) → ℝ)
        (JR : JuntaRep N) (q : ℕ) (T : ℝ),
      1 ≤ q ∧
      HasNonnegativeAxiomRepresentation F P ∧
      JR.Nonnegative ∧
      JR.DegreeLE degree ∧
      (∀ z, P z = 1 + JR.eval z + E z) ∧
      (∀ z, 0 ≤ JR.eval z ∧ JR.eval z ≤ T) ∧
      (∀ z,
        0 ≤ E z ∧
        E z ≤ T * decompositionError degree) ∧
      T ≤ (2 : ℝ) * π.length := by
  obtain ⟨P, J, E, q, T, hq, hP, hidentity, hJ, hJbound, hEbound, hT⟩ :=
    revres_to_robust_identity π degree
  obtain ⟨JR, hJRnonnegative, hJRdegree, hJReval⟩ :=
    exists_juntaRep_of_isConicalJunta hJ
  refine ⟨P, E, JR, q, T, hq, hP, hJRnonnegative, hJRdegree, ?_, ?_, hEbound, hT⟩
  · intro z
    rw [hJReval]
    exact hidentity z
  · intro z
    rw [hJReval]
    exact hJbound z

/-- If the worst possible robust-identity error is below the amplification threshold, the junta
growth lower bound transfers directly to refutation length. -/
theorem revres_lower_bound_of_amplification_small_error
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    {degree : ℕ}
    {errorCap growth : ℝ}
    (hAmp : RobustAmplificationProperty F degree errorCap growth)
    (hsmall :
      (2 : ℝ) * π.length * decompositionError degree ≤ errorCap) :
    growth ≤ (2 : ℝ) * π.length := by
  obtain ⟨P, E, JR, _q, T, _hq, hP, hJRnonnegative, hJRdegree, hidentity,
      hJRbound, hEbound, hT⟩ :=
    revres_to_explicit_robust_identity π degree
  have hEcap : ∀ z, 0 ≤ E z ∧ E z ≤ errorCap := by
    intro z
    refine ⟨(hEbound z).1, ?_⟩
    calc
      E z ≤ T * decompositionError degree := (hEbound z).2
      _ ≤ ((2 : ℝ) * π.length) * decompositionError degree :=
        mul_le_mul_of_nonneg_right hT (decompositionError_nonneg degree)
      _ ≤ errorCap := hsmall
  obtain ⟨z, hgrowth⟩ :=
    hAmp P E JR hP hJRnonnegative hJRdegree hidentity hEcap
  exact hgrowth.trans ((hJRbound z).2.trans hT)

/-- Either amplification already forces a long refutation, or the robust-identity error scale is
larger than the permitted error cap. -/
theorem revres_lower_bound_dichotomy
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    {degree : ℕ}
    {errorCap growth : ℝ}
    (hAmp : RobustAmplificationProperty F degree errorCap growth) :
    growth ≤ (2 : ℝ) * π.length ∨
      errorCap < (2 : ℝ) * π.length * decompositionError degree := by
  by_cases hsmall :
      (2 : ℝ) * π.length * decompositionError degree ≤ errorCap
  · exact Or.inl (revres_lower_bound_of_amplification_small_error π hAmp hsmall)
  · exact Or.inr (lt_of_not_ge hsmall)

/-- Exact scale bound combining the growth and large-error branches. -/
theorem revres_scale_bound_of_amplification
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    {degree : ℕ}
    {errorCap growth : ℝ}
    (hAmp : RobustAmplificationProperty F degree errorCap growth) :
    min growth (errorCap / decompositionError degree) ≤
      (2 : ℝ) * π.length := by
  rcases revres_lower_bound_dichotomy π hAmp with hgrowth | herror
  · exact (min_le_left growth (errorCap / decompositionError degree)).trans hgrowth
  · have hquotient :
        errorCap / decompositionError degree < (2 : ℝ) * π.length :=
      (div_lt_iff₀ (decompositionError_pos degree)).2 herror
    exact (min_le_right growth (errorCap / decompositionError degree)).trans hquotient.le

/-- **Milestone M4.** Any robust amplification property with parameters `errorCap` and `growth`
gives a finite lower bound on the length of every RevRes refutation of the truth-table lift. -/
theorem revres_lower_bound_of_amplification
    {F : CNF N}
    (π : RevResRefutation (indexLift F))
    {degree : ℕ}
    {errorCap growth : ℝ}
    (hAmp : RobustAmplificationProperty F degree errorCap growth) :
    (1 / 2 : ℝ) * min growth (errorCap / decompositionError degree) ≤
      (π.length : ℝ) := by
  have hscale := revres_scale_bound_of_amplification π hAmp
  linarith

end Revres
