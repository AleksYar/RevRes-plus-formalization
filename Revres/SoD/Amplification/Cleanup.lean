import Revres.SoD.Amplification.Rewire

/-!
# Cleanup averaging

Count the next-row candidate boxes avoided by each term, retain the corresponding
sub-juntas, and select a candidate that preserves a constant fraction of the
current junta value.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace SoD

namespace Amplification

variable {ell degree : ℕ}

namespace Term

/-- A term avoids a macrobox when it fixes no encoded coordinate in that box. -/
def AvoidsBox (hell : 0 < ell)
    (t : Term (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell)) : Prop :=
  Disjoint t.support (boxBits hell R)

instance avoidsBoxDecidable (hell : 0 < ell)
    (t : Term (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell)) : Decidable (AvoidsBox hell t R) := by
  unfold AvoidsBox
  infer_instance

theorem avoidsBox_iff {hell : 0 < ell}
    {t : Term (Encoding.variableCount (2 * ell))}
    {R : GridNode (ActiveEdge.localOrder ell)} :
    AvoidsBox hell t R ↔ ∀ i ∈ t.support, i ∉ boxBits hell R := by
  simp [AvoidsBox, Finset.disjoint_left]

theorem not_avoidsBox_iff {hell : 0 < ell}
    {t : Term (Encoding.variableCount (2 * ell))}
    {R : GridNode (ActiveEdge.localOrder ell)} :
    ¬AvoidsBox hell t R ↔
      ∃ i, i ∈ t.support ∧ i ∈ boxBits hell R := by
  exact Finset.not_disjoint_iff

theorem indicator_eq_of_avoidsBox {hell : 0 < ell}
    {t : Term (Encoding.variableCount (2 * ell))}
    {R : GridNode (ActiveEdge.localOrder ell)}
    {x y : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2}
    (havoid : AvoidsBox hell t R)
    (hagree : ∀ i, i ∉ boxBits hell R → x i = y i) :
    t.indicator x = t.indicator y := by
  have hmatches : t.Matches x ↔ t.Matches y := by
    constructor
    · intro hx i b hib
      have hi : i ∈ t.support := Term.mem_support.mpr (by simp [hib])
      exact (hagree i ((avoidsBox_iff.mp havoid) i hi)).symm.trans (hx i b hib)
    · intro hy i b hib
      have hi : i ∈ t.support := Term.mem_support.mpr (by simp [hib])
      exact (hagree i ((avoidsBox_iff.mp havoid) i hi)).trans (hy i b hib)
  simp only [Term.indicator]
  rw [if_congr hmatches rfl rfl]

/-- Next-row candidates whose encoded blocks meet the support of `t`. -/
noncomputable def metCandidates (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    Finset (GridNode (ActiveEdge.localOrder ell)) := by
  classical
  exact (SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q).filter
    fun R => ¬AvoidsBox hell t R

/-- Next-row candidates whose encoded blocks are disjoint from the support of `t`. -/
noncomputable def avoidedCandidates (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    Finset (GridNode (ActiveEdge.localOrder ell)) := by
  classical
  exact (SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q).filter
    fun R => AvoidsBox hell t R

theorem mem_metCandidates_iff {hell : 0 < ell}
    {Q R : GridNode (ActiveEdge.localOrder ell)}
    {t : Term (Encoding.variableCount (2 * ell))} :
    R ∈ metCandidates hell Q t ↔
      R ∈ SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q ∧
        ¬AvoidsBox hell t R := by
  classical
  simp [metCandidates]

theorem mem_avoidedCandidates_iff {hell : 0 < ell}
    {Q R : GridNode (ActiveEdge.localOrder ell)}
    {t : Term (Encoding.variableCount (2 * ell))} :
    R ∈ avoidedCandidates hell Q t ↔
      R ∈ SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q ∧
        AvoidsBox hell t R := by
  classical
  simp [avoidedCandidates]

theorem metCandidates_card_add_avoidedCandidates_card
    (hell : 0 < ell) (Q : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    (metCandidates hell Q t).card + (avoidedCandidates hell Q t).card =
      (SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q).card := by
  classical
  simpa [metCandidates, avoidedCandidates, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q)
      (p := fun R => AvoidsBox hell t R))

theorem metCandidates_card_le_degree
    (hell : 0 < ell) (Q : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    (metCandidates hell Q t).card ≤ t.degree := by
  classical
  let chosenBit : ↑(metCandidates hell Q t) →
      Fin (Encoding.variableCount (2 * ell)) := fun R =>
    Classical.choose
      (not_avoidsBox_iff.mp (mem_metCandidates_iff.mp R.property).2)
  have chosenBit_spec (R : ↑(metCandidates hell Q t)) :
      chosenBit R ∈ t.support ∧ chosenBit R ∈ boxBits hell R.1 :=
    Classical.choose_spec
      (not_avoidsBox_iff.mp (mem_metCandidates_iff.mp R.property).2)
  let supportBit : ↑(metCandidates hell Q t) → ↑t.support := fun R =>
    ⟨chosenBit R, (chosenBit_spec R).1⟩
  have hinjective : Function.Injective supportBit := by
    intro R S hRS
    apply Subtype.ext
    by_contra hne
    have hbit : chosenBit R = chosenBit S := congrArg Subtype.val hRS
    have hdisjoint : Disjoint (boxBits hell R.1) (boxBits hell S.1) :=
      boxBits_disjoint hne
    exact (Finset.disjoint_left.mp hdisjoint)
      (chosenBit_spec R).2 (by simpa [hbit] using (chosenBit_spec S).2)
  have hcard := Fintype.card_le_of_injective supportBit hinjective
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  simpa [Term.degree] using hcard

theorem term_avoids_many_candidates
    (hell : 0 < ell) (Q : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    (SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q).card - t.degree ≤
      (avoidedCandidates hell Q t).card := by
  have hpartition := metCandidates_card_add_avoidedCandidates_card hell Q t
  have hmet := metCandidates_card_le_degree hell Q t
  omega

theorem term_avoids_many_candidates_of_internal
    (hell : 0 < ell) (Q : GridNode (ActiveEdge.localOrder ell))
    (hQ : Q.IsInternal)
    (t : Term (Encoding.variableCount (2 * ell))) :
    (ActiveEdge.localOrder ell - 1) - t.degree ≤
      (avoidedCandidates hell Q t).card := by
  rw [← SoD.nextMacroRowCandidates_card (BinaryPointer.order_pos hell) Q hQ]
  exact term_avoids_many_candidates hell Q t

end Term

namespace JuntaRep

/-- Retain exactly the supported terms whose coordinates avoid `R`. -/
noncomputable def avoidingBox (hell : 0 < ell)
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell)) :
    JuntaRep (Encoding.variableCount (2 * ell)) := by
  classical
  exact JR.filter fun t => Term.AvoidsBox hell t R

theorem mem_support_avoidingBox {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    {R : GridNode (ActiveEdge.localOrder ell)}
    {t : Term (Encoding.variableCount (2 * ell))} :
    t ∈ (avoidingBox hell JR R).support ↔
      t ∈ JR.support ∧ Term.AvoidsBox hell t R := by
  classical
  simp [avoidingBox]

theorem avoidingBox_apply (hell : 0 < ell)
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell))
    (t : Term (Encoding.variableCount (2 * ell))) :
    avoidingBox hell JR R t =
      if Term.AvoidsBox hell t R then JR t else 0 := by
  classical
  rw [avoidingBox, Finsupp.filter_apply]

theorem avoidingBox_nonnegative {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.Nonnegative) (R : GridNode (ActiveEdge.localOrder ell)) :
    (avoidingBox hell JR R).Nonnegative := by
  intro t
  rw [avoidingBox_apply]
  split <;> simp_all [hJR t]

theorem avoidingBox_degreeLE {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.DegreeLE degree) (R : GridNode (ActiveEdge.localOrder ell)) :
    (avoidingBox hell JR R).DegreeLE degree := by
  intro t ht
  exact hJR t (mem_support_avoidingBox.mp ht).1

theorem avoidingBox_nodeAligned {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.NodeAligned) (R : GridNode (ActiveEdge.localOrder ell)) :
    (avoidingBox hell JR R).NodeAligned := by
  intro t ht
  exact hJR t (mem_support_avoidingBox.mp ht).1

theorem avoidingBox_exitCurious {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.ExitCurious hell) (R : GridNode (ActiveEdge.localOrder ell)) :
    (avoidingBox hell JR R).ExitCurious hell := by
  intro t ht
  exact hJR t (mem_support_avoidingBox.mp ht).1

theorem avoidingBox_nonWitnessing {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (R : GridNode (ActiveEdge.localOrder ell)) :
    (avoidingBox hell JR R).NonWitnessing (Preprocess.cleaningFormula hell) := by
  intro t ht
  exact hJR t (mem_support_avoidingBox.mp ht).1

theorem eval_avoidingBox_nonneg {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.Nonnegative) (R : GridNode (ActiveEdge.localOrder ell))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    0 ≤ (avoidingBox hell JR R).eval z :=
  Revres.JuntaRep.eval_nonneg (avoidingBox_nonnegative hJR R) z

theorem eval_avoidingBox_le {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hJR : JR.Nonnegative) (R : GridNode (ActiveEdge.localOrder ell))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (avoidingBox hell JR R).eval z ≤ JR.eval z := by
  classical
  let remainder := JR.filter fun t => ¬Term.AvoidsBox hell t R
  have hpartition : avoidingBox hell JR R + remainder = JR := by
    exact Finsupp.filter_add_filter_not JR (fun t => Term.AvoidsBox hell t R)
  have hremainder : Revres.JuntaRep.Nonnegative remainder := by
    intro t
    dsimp only [remainder]
    rw [Finsupp.filter_apply]
    split <;> simp_all [hJR t]
  calc
    (avoidingBox hell JR R).eval z ≤
        (avoidingBox hell JR R).eval z + Revres.JuntaRep.eval remainder z :=
      le_add_of_nonneg_right (Revres.JuntaRep.eval_nonneg hremainder z)
    _ = (avoidingBox hell JR R + remainder).eval z :=
      (Revres.JuntaRep.eval_add _ _ z).symm
    _ = JR.eval z := congrArg (fun KR : JuntaRep (Encoding.variableCount (2 * ell)) =>
      Revres.JuntaRep.eval KR z) hpartition

theorem eval_avoidingBox_eq_of_agrees_outside {hell : 0 < ell}
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell))
    {x y : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2}
    (hagree : ∀ i, i ∉ boxBits hell R → x i = y i) :
    (avoidingBox hell JR R).eval x = (avoidingBox hell JR R).eval y := by
  classical
  rw [Revres.JuntaRep.eval, Revres.JuntaRep.eval, Finsupp.sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Term.indicator_eq_of_avoidsBox
    (mem_support_avoidingBox.mp ht).2 hagree]

theorem eval_avoidingBox_eq_sum_filter (hell : 0 < ell)
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (R : GridNode (ActiveEdge.localOrder ell))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (avoidingBox hell JR R).eval z =
      ∑ t ∈ JR.support.filter (fun t => Term.AvoidsBox hell t R),
        JR t * t.indicator z := by
  classical
  rw [Revres.JuntaRep.eval, avoidingBox, Finsupp.sum_filter_index,
    Finsupp.support_filter]

theorem sum_eval_avoidingBox_eq (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell))
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (∑ R ∈ SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q,
        (avoidingBox hell JR R).eval z) =
      ∑ t ∈ JR.support,
        ((Term.avoidedCandidates hell Q t).card : ℝ) *
          (JR t * t.indicator z) := by
  classical
  let candidates := SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q
  calc
    (∑ R ∈ candidates, (avoidingBox hell JR R).eval z) =
        ∑ R ∈ candidates,
          ∑ t ∈ JR.support.filter (fun t => Term.AvoidsBox hell t R),
            JR t * t.indicator z := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact eval_avoidingBox_eq_sum_filter hell JR R z
    _ = ∑ R ∈ candidates, ∑ t ∈ JR.support,
          if Term.AvoidsBox hell t R then JR t * t.indicator z else 0 := by
      apply Finset.sum_congr rfl
      intro R _hR
      rw [Finset.sum_filter]
    _ = ∑ t ∈ JR.support, ∑ R ∈ candidates,
          if Term.AvoidsBox hell t R then JR t * t.indicator z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ JR.support,
        ((Term.avoidedCandidates hell Q t).card : ℝ) *
          (JR t * t.indicator z) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [← Finset.sum_filter]
      simp [Term.avoidedCandidates, candidates, Finset.sum_const, nsmul_eq_mul]

theorem sum_eval_avoidingBox_lower_bound (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell))
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hNonnegative : JR.Nonnegative) (hDegree : JR.DegreeLE degree)
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (((SoD.nextMacroRowCandidates
        (BinaryPointer.order_pos hell) Q).card - degree : ℕ) : ℝ) * JR.eval z ≤
      ∑ R ∈ SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q,
        (avoidingBox hell JR R).eval z := by
  classical
  rw [sum_eval_avoidingBox_eq hell Q JR z, Revres.JuntaRep.eval,
    Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hcount :
      (SoD.nextMacroRowCandidates
          (BinaryPointer.order_pos hell) Q).card - degree ≤
        (Term.avoidedCandidates hell Q t).card :=
    (Nat.sub_le_sub_left (hDegree t ht) _).trans
      (Term.term_avoids_many_candidates hell Q t)
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hcount
  · exact mul_nonneg (hNonnegative t) (Term.indicator_nonneg t z)

theorem sum_one_add_eval_avoidingBox_lower_bound (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell))
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hNonnegative : JR.Nonnegative) (hDegree : JR.DegreeLE degree)
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (((SoD.nextMacroRowCandidates
        (BinaryPointer.order_pos hell) Q).card - degree : ℕ) : ℝ) *
        (1 + JR.eval z) ≤
      ∑ R ∈ SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q,
        (1 + (avoidingBox hell JR R).eval z) := by
  let candidates := SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q
  have heval := sum_eval_avoidingBox_lower_bound hell Q hNonnegative hDegree z
  have hcard :
      (((candidates.card - degree : ℕ) : ℝ)) ≤ (candidates.card : ℝ) := by
    exact_mod_cast Nat.sub_le candidates.card degree
  calc
    (((candidates.card - degree : ℕ) : ℝ)) * (1 + JR.eval z) =
        ((candidates.card - degree : ℕ) : ℝ) +
          ((candidates.card - degree : ℕ) : ℝ) * JR.eval z := by ring
    _ ≤ (candidates.card : ℝ) +
        ∑ R ∈ candidates, (avoidingBox hell JR R).eval z :=
      add_le_add hcard heval
    _ = ∑ R ∈ candidates, (1 + (avoidingBox hell JR R).eval z) := by
      simp [Finset.sum_add_distrib]

/-- Some next-row candidate retains at least `49 / 50` of `1 + JR.eval z`. -/
theorem exists_candidate_retaining_eval (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell)) (hQ : Q.IsInternal)
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    (hNonnegative : JR.Nonnegative) (hDegree : JR.DegreeLE degree)
    (hsmall : 100 * degree ≤ ActiveEdge.localOrder ell)
    (z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    ∃ R,
      ∃ _hR : R ∈ SoD.nextMacroRowCandidates
          (BinaryPointer.order_pos hell) Q,
        (49 / 50 : ℝ) * (1 + JR.eval z) ≤
          1 + (avoidingBox hell JR R).eval z := by
  classical
  let candidates := SoD.nextMacroRowCandidates (BinaryPointer.order_pos hell) Q
  have horder : 1 < ActiveEdge.localOrder ell := by
    unfold GridNode.IsInternal at hQ
    omega
  have hcard : candidates.card = ActiveEdge.localOrder ell - 1 :=
    SoD.nextMacroRowCandidates_card (BinaryPointer.order_pos hell) Q hQ
  have hnonempty : candidates.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    omega
  have hhalf : 50 * degree ≤ candidates.card := by
    rw [hcard]
    by_cases hzero : degree = 0
    · simp [hzero]
    · have hdegree_pos : 0 < degree := Nat.pos_of_ne_zero hzero
      omega
  have hcount_ratio :
      (candidates.card : ℝ) * (49 / 50 : ℝ) ≤
        ((candidates.card - degree : ℕ) : ℝ) := by
    have hnat :
        49 * candidates.card ≤ 50 * (candidates.card - degree) := by
      omega
    have hreal :
        (49 : ℝ) * candidates.card ≤
          (50 : ℝ) * ((candidates.card - degree : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  have hone_nonneg : 0 ≤ 1 + JR.eval z := by
    have := Revres.JuntaRep.eval_nonneg hNonnegative z
    linarith
  have hsum :
      (((candidates.card - degree : ℕ) : ℝ)) * (1 + JR.eval z) ≤
        candidates.sum (fun R => 1 + (avoidingBox hell JR R).eval z) := by
    simpa [candidates] using sum_one_add_eval_avoidingBox_lower_bound
      hell Q hNonnegative hDegree z
  by_contra hnone
  have hterm (R : GridNode (ActiveEdge.localOrder ell)) (hR : R ∈ candidates) :
      1 + (avoidingBox hell JR R).eval z <
        (49 / 50 : ℝ) * (1 + JR.eval z) := by
    apply lt_of_not_ge
    intro hretain
    exact hnone ⟨R, hR, hretain⟩
  have hsum_lt :
      candidates.sum (fun R => 1 + (avoidingBox hell JR R).eval z) <
        (candidates.card : ℝ) *
          ((49 / 50 : ℝ) * (1 + JR.eval z)) := by
    calc
      candidates.sum (fun R => 1 + (avoidingBox hell JR R).eval z) <
          candidates.sum (fun _R => (49 / 50 : ℝ) * (1 + JR.eval z)) :=
        Finset.sum_lt_sum_of_nonempty hnonempty hterm
      _ = (candidates.card : ℝ) *
          ((49 / 50 : ℝ) * (1 + JR.eval z)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hscaled :
      (candidates.card : ℝ) *
          ((49 / 50 : ℝ) * (1 + JR.eval z)) ≤
        ((candidates.card - degree : ℕ) : ℝ) * (1 + JR.eval z) := by
    calc
      (candidates.card : ℝ) *
          ((49 / 50 : ℝ) * (1 + JR.eval z)) =
          ((candidates.card : ℝ) * (49 / 50 : ℝ)) *
            (1 + JR.eval z) := by ring
      _ ≤ ((candidates.card - degree : ℕ) : ℝ) * (1 + JR.eval z) :=
        mul_le_mul_of_nonneg_right hcount_ratio hone_nonneg
  exact (not_lt_of_ge hsum) (hsum_lt.trans_le hscaled)

/-- The terms avoiding `R` cannot observe the candidate stage rewire. -/
theorem eval_avoidingBox_stage_rewire_eq
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (R : GridNode (ActiveEdge.localOrder ell))
    (hR : R ∈ SoD.nextMacroRowCandidates
      (BinaryPointer.order_pos hell) s.currentBox)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell)) :
    (avoidingBox hell JR R).eval (stageAssignment hgood hinternal y) =
      (avoidingBox hell JR R).eval
        (rewiredStageAssignment hgood hinternal y R hR) := by
  exact eval_rewire_eq (stageRewireSpec hgood hinternal y R hR)
    (avoidingBox_nodeAligned hAlign R)
    (avoidingBox_exitCurious hCurious R)
    (avoidingBox_nonWitnessing hNonWitness R)

end JuntaRep

/-- A cleanup candidate preserves strict `7 / 5` growth after rewiring and on
every assignment that agrees with the rewired assignment outside that box. -/
theorem exists_candidate_cleanup_growth
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal)
    (y : Fin (SoPL.Encoding.variableCount ell) → Lemma53.F2)
    (hNonnegative : JR.Nonnegative) (hDegree : JR.DegreeLE degree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * degree ≤ ActiveEdge.localOrder ell)
    (hgrowth :
      ((3 / 2 : ℝ) - errorThreshold) * s.B <
        1 + JR.eval (stageAssignment hgood hinternal y)) :
    ∃ R,
      ∃ hR : R ∈ SoD.nextMacroRowCandidates
          (BinaryPointer.order_pos hell) s.currentBox,
        let beta := rewiredStageAssignment hgood hinternal y R hR
        (7 / 5 : ℝ) * s.B <
            1 + (JuntaRep.avoidingBox hell JR R).eval beta ∧
          ∀ z,
            (∀ i, i ∉ boxBits hell R → z i = beta i) →
            (7 / 5 : ℝ) * s.B < 1 + JR.eval z := by
  let alpha := stageAssignment hgood hinternal y
  obtain ⟨R, hR, hretain⟩ := JuntaRep.exists_candidate_retaining_eval
    hell s.currentBox hinternal hNonnegative hDegree hsmall alpha
  let beta := rewiredStageAssignment hgood hinternal y R hR
  have hconstant :
      (7 / 5 : ℝ) <
        (49 / 50 : ℝ) * ((3 / 2 : ℝ) - errorThreshold) := by
    norm_num [errorThreshold]
  have hbefore :
      (7 / 5 : ℝ) * s.B <
        (49 / 50 : ℝ) * (1 + JR.eval alpha) := by
    have hconstant_scaled := mul_lt_mul_of_pos_right hconstant hgood.B_pos
    have hgrowth_scaled := mul_lt_mul_of_pos_left hgrowth
      (by norm_num : (0 : ℝ) < 49 / 50)
    calc
      (7 / 5 : ℝ) * s.B <
          ((49 / 50 : ℝ) * ((3 / 2 : ℝ) - errorThreshold)) * s.B :=
        hconstant_scaled
      _ = (49 / 50 : ℝ) *
          (((3 / 2 : ℝ) - errorThreshold) * s.B) := by ring
      _ < (49 / 50 : ℝ) * (1 + JR.eval alpha) := hgrowth_scaled
  have hstage :
      (7 / 5 : ℝ) * s.B <
        1 + (JuntaRep.avoidingBox hell JR R).eval alpha :=
    hbefore.trans_le hretain
  have hrewire :
      (JuntaRep.avoidingBox hell JR R).eval alpha =
        (JuntaRep.avoidingBox hell JR R).eval beta := by
    exact JuntaRep.eval_avoidingBox_stage_rewire_eq
      hgood hinternal y R hR hAlign hCurious hNonWitness
  have hbeta :
      (7 / 5 : ℝ) * s.B <
        1 + (JuntaRep.avoidingBox hell JR R).eval beta := by
    rw [← hrewire]
    exact hstage
  refine ⟨R, hR, ?_⟩
  change (7 / 5 : ℝ) * s.B <
      1 + (JuntaRep.avoidingBox hell JR R).eval beta ∧
    ∀ z, (∀ i, i ∉ boxBits hell R → z i = beta i) →
      (7 / 5 : ℝ) * s.B < 1 + JR.eval z
  refine ⟨hbeta, ?_⟩
  intro z hagree
  have hinvariant :
      (JuntaRep.avoidingBox hell JR R).eval z =
        (JuntaRep.avoidingBox hell JR R).eval beta :=
    JuntaRep.eval_avoidingBox_eq_of_agrees_outside JR R hagree
  have hsub :
      (7 / 5 : ℝ) * s.B <
        1 + (JuntaRep.avoidingBox hell JR R).eval z := by
    rw [hinvariant]
    exact hbeta
  have hfull := JuntaRep.eval_avoidingBox_le (hell := hell) hNonnegative R z
  linarith

end Amplification

end SoD

end Revres
