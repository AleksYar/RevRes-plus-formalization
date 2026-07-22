import Revres.SoD.Amplification.State
import Revres.SoD.Preprocess.Main
import Revres.SoPL.Hardness

/-!
# Restricted certificates and amplification growth

The active-edge formulation restricts the cleaned ambient certificate to SoPL.
The explicit support-local hardness hypothesis then supplies a path-family input
on which the robust identity grows. Rewiring and cleanup are intentionally absent.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

variable {ell proofDegree degreeLowerBound : ℕ}

/-- The encoded active-edge assignment at a good nonterminal state. -/
noncomputable def stageAssignment {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  ActiveEdge.embeddedAssignment (hgood.toStageContext hinternal) y

@[simp]
theorem stageAssignment_eq_embeddedAssignment {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    stageAssignment hgood hinternal y =
      ActiveEdge.embeddedAssignment (hgood.toStageContext hinternal) y :=
  rfl

theorem stageAssignment_matches {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    s.restriction.Matches (stageAssignment hgood hinternal y) := by
  apply Restriction.matches_of_eq_nullAssignment_on_fixed
  intro i b hib
  have hi : i ∉ boxBits hell s.currentBox := by
    intro himem
    have hnone := (hgood.structural.free_current i).mpr himem
    rw [hib] at hnone
    simp at hnone
  have hnode :
      Encoding.nodeOfBit (2 * ell) i ∉
        ActiveEdge.embeddedSubgrid hell s.currentBox := by
    intro hmem
    exact hi (mem_boxBits_iff.mpr hmem)
  let ctx := hgood.toStageContext hinternal
  let source := SoPL.Encoding.decodeInput ell y
  have houtside :
      (ActiveEdge.activeEdgeEmbedding ctx source).successor
          (Encoding.nodeOfBit (2 * ell) i) =
        s.nullInput.successor (Encoding.nodeOfBit (2 * ell) i) := by
    simpa [ctx] using ActiveEdge.activeEdgeEmbedding_outside ctx source hnode
  have houtside' :
      (ActiveEdge.activeEdgeEmbedding ctx source).successor
          ((Encoding.bitIndexEquiv (2 * ell)).symm i).1 =
        s.nullInput.successor ((Encoding.bitIndexEquiv (2 * ell)).symm i).1 := by
    simpa [Encoding.nodeOfBit] using houtside
  calc
    stageAssignment hgood hinternal y i =
        Encoding.encodeInput (ActiveEdge.activeEdgeEmbedding ctx source) i := rfl
    _ = Encoding.encodeInput s.nullInput i := by
      simp only [Encoding.encodeInput]
      rw [houtside']
    _ = s.restriction.nullAssignment i := by
      exact congrFun (Restriction.encodeInput_nullInput s.restriction) i

theorem GoodState.bound_le_one_add_eval_stageAssignment {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2) :
    s.B ≤ 1 + JR.eval (stageAssignment hgood hinternal y) :=
  hgood.numerical _ (stageAssignment_matches hgood hinternal y)

theorem GoodState.B_pos {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) : 0 < s.B :=
  lt_of_lt_of_le zero_lt_one hgood.one_le_B

/-- Transfer the cleaned ambient certificate through the active-edge formulation. -/
theorem restricted_certificate {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree) :
    HasNSCertificateDegreeLE
      (SoPL.Encoding.searchCNF ell hell)
      (fun y ↦ P (stageAssignment hgood hinternal y))
      (2 * proofDegree * (7 * ell)) := by
  have hambient :
      HasNSCertificateDegreeLE
        (Encoding.searchCNF (2 * ell) (ActiveEdge.ambientWidth_pos hell))
        P proofDegree := by
    simpa [Preprocess.cleaningFormula] using hcert
  have htransferred := hasCertificateDegreeLE_transfer
    (ActiveEdge.activeEdgeFormulation (hgood.toStageContext hinternal)) hambient
  simpa [stageAssignment, ActiveEdge.activeEdgeFormulation_mapInput] using htransferred

/-- Normalize the restricted certificate by the positive state bound. -/
theorem normalized_restricted_certificate {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree) :
    HasNSCertificateDegreeLE
      (SoPL.Encoding.searchCNF ell hell)
      (fun y ↦ P (stageAssignment hgood hinternal y) / s.B)
      (2 * proofDegree * (7 * ell)) := by
  have hrestricted := restricted_certificate hgood hinternal hcert
  have hscaled := hasCertificateDegreeLE_scale s.B⁻¹ hrestricted
  simpa [div_eq_mul_inv, mul_comm] using hscaled

/-- The fixed error threshold used by robust growth. -/
noncomputable def errorThreshold : ℝ := 1 / 100

/-- The robust error is pointwise nonnegative and at most `1 / 100`. -/
def ErrorControlled
    (E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ) : Prop :=
  ∀ z, 0 ≤ E z ∧ E z ≤ errorThreshold

@[simp]
theorem errorThreshold_pos : 0 < errorThreshold := by
  norm_num [errorThreshold]

theorem errorThreshold_le_one : errorThreshold ≤ 1 := by
  norm_num [errorThreshold]

theorem one_lt_three_halves_sub_errorThreshold :
    (1 : ℝ) < 3 / 2 - errorThreshold := by
  norm_num [errorThreshold]

/-- A low-degree restricted certificate must grow on one encoded hard path input. -/
theorem exists_path_input_growth {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (hdegree : 2 * proofDegree * (7 * ell) < degreeLowerBound) :
    ∃ y, SoPL.IsEncodedPathFamily ell hell y ∧
      (3 / 2 : ℝ) * s.B < P (stageAssignment hgood hinternal y) ∧
      ((3 / 2 : ℝ) - errorThreshold) * s.B <
        1 + JR.eval (stageAssignment hgood hinternal y) := by
  obtain ⟨cert, hcertDegree⟩ :=
    normalized_restricted_certificate hgood hinternal hcert
  have hcert_lt : cert.degree < degreeLowerBound :=
    lt_of_le_of_lt hcertDegree hdegree
  have hexists :
      ∃ y, SoPL.IsEncodedPathFamily ell hell y ∧
        (3 / 2 : ℝ) * s.B < P (stageAssignment hgood hinternal y) := by
    by_contra hnone
    have hupper : ∀ y, SoPL.IsEncodedPathFamily ell hell y →
        P (stageAssignment hgood hinternal y) ≤ (3 / 2 : ℝ) * s.B := by
      intro y hy
      exact le_of_not_gt fun hgrowth => hnone ⟨y, hy, hgrowth⟩
    have happrox : ∀ y, SoPL.IsEncodedPathFamily ell hell y →
        (1 / 2 : ℝ) ≤ P (stageAssignment hgood hinternal y) / s.B ∧
          P (stageAssignment hgood hinternal y) / s.B ≤ (3 / 2 : ℝ) := by
      intro y hy
      let alpha := stageAssignment hgood hinternal y
      have hJ : s.B ≤ 1 + JR.eval alpha :=
        hgood.bound_le_one_add_eval_stageAssignment hinternal y
      have hE := herror alpha
      have hP : s.B ≤ P alpha := by
        rw [hidentity alpha]
        linarith
      constructor
      · apply (le_div_iff₀ hgood.B_pos).2
        nlinarith [hgood.one_le_B]
      · apply (div_le_iff₀ hgood.B_pos).2
        exact hupper y hy
    exact (hHard.not_approximate_of_degree_lt cert hcert_lt) happrox
  obtain ⟨y, hy, hgrowth⟩ := hexists
  let alpha := stageAssignment hgood hinternal y
  have hE := herror alpha
  have herror_scaled : E alpha ≤ errorThreshold * s.B := by
    calc
      E alpha ≤ errorThreshold := hE.2
      _ ≤ errorThreshold * s.B := by
        simpa using mul_le_mul_of_nonneg_left hgood.one_le_B
          (le_of_lt errorThreshold_pos)
  refine ⟨y, hy, hgrowth, ?_⟩
  rw [hidentity alpha] at hgrowth
  change ((3 / 2 : ℝ) - errorThreshold) * s.B < 1 + JR.eval alpha
  nlinarith

end Amplification

end SoD

end Revres
