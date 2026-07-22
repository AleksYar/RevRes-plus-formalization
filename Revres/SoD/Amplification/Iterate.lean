import Revres.SoD.Amplification.Step

/-!
# Iterated amplification

Iterate the one-step theorem through every legal macro-row while tracking the
exact stage and the concrete `(7 / 5)` power bound.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

variable {ell proofDegree degreeLowerBound juntaDegree : ℕ}

namespace GoodState

/-- A good state is nonterminal when its stage has room for one more row. -/
theorem currentBox_internal_of_stage_succ_lt
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s)
    (hroom : s.stage + 1 < ActiveEdge.localOrder ell) :
    s.currentBox.IsInternal := by
  unfold GridNode.IsInternal
  rw [hgood.row_eq_stage]
  exact hroom

end GoodState

/-- Iterate from any good state while the resulting stage remains in the
macrogrid. -/
theorem amplification_iterate_from
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hgood : GoodState hell JR s)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree : 2 * proofDegree * (7 * ell) < degreeLowerBound)
    (hNonnegative : JR.Nonnegative)
    (hJuntaDegree : JR.DegreeLE juntaDegree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * juntaDegree ≤ ActiveEdge.localOrder ell)
    (steps : ℕ) (hroom : s.stage + steps < ActiveEdge.localOrder ell) :
    ∃ next, GoodState hell JR next ∧
      next.stage = s.stage + steps ∧
        (7 / 5 : ℝ) ^ steps * s.B ≤ next.B := by
  induction steps generalizing s with
  | zero =>
      refine ⟨s, hgood, by simp, ?_⟩
      simp
  | succ k ih =>
      have hroomMiddle : s.stage + k < ActiveEdge.localOrder ell := by
        omega
      obtain ⟨middle, hmiddleGood, hmiddleStage, hmiddleBound⟩ :=
        ih hgood hroomMiddle
      have hmiddleRoom : middle.stage + 1 < ActiveEdge.localOrder ell := by
        rw [hmiddleStage]
        omega
      have hmiddleInternal : middle.currentBox.IsInternal :=
        hmiddleGood.currentBox_internal_of_stage_succ_lt hmiddleRoom
      obtain ⟨next, hnextGood, hnextStage, hnextBound⟩ := amplification_step
        hmiddleGood hmiddleInternal hcert hidentity herror hHard htransferDegree
          hNonnegative hJuntaDegree hAlign hCurious hNonWitness hsmall
      refine ⟨next, hnextGood, ?_, ?_⟩
      · rw [hnextStage, hmiddleStage]
        omega
      · have hscaled := mul_le_mul_of_nonneg_left hmiddleBound
          (by norm_num : (0 : ℝ) ≤ 7 / 5)
        calc
          (7 / 5 : ℝ) ^ (Nat.succ k) * s.B =
              (7 / 5 : ℝ) * ((7 / 5 : ℝ) ^ k * s.B) := by
            rw [pow_succ]
            ring
          _ ≤ (7 / 5 : ℝ) * middle.B := hscaled
          _ ≤ next.B := hnextBound

/-- Starting from the canonical base state, every legal stage has a good state
with the corresponding power lower bound. -/
theorem amplification_iterate
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hlocal : 1 < ActiveEdge.localOrder ell)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree : 2 * proofDegree * (7 * ell) < degreeLowerBound)
    (hNonnegative : JR.Nonnegative)
    (hJuntaDegree : JR.DegreeLE juntaDegree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * juntaDegree ≤ ActiveEdge.localOrder ell)
    (k : ℕ) (hk : k < ActiveEdge.localOrder ell) :
    ∃ state, GoodState hell JR state ∧ state.stage = k ∧
      (7 / 5 : ℝ) ^ k ≤ state.B := by
  have hbase : GoodState hell JR (baseState hell) :=
    good_baseState hell hlocal JR hNonnegative
  obtain ⟨state, hstateGood, hstateStage, hstateBound⟩ :=
    amplification_iterate_from hbase hcert hidentity herror hHard
      htransferDegree hNonnegative hJuntaDegree hAlign hCurious hNonWitness
      hsmall k (by simpa [baseState] using hk)
  refine ⟨state, hstateGood, ?_, ?_⟩
  · simpa [baseState] using hstateStage
  · simpa [baseState] using hstateBound

/-- The last macro-row is reached after exactly `localOrder ell - 1` steps. -/
theorem exists_last_amplification_state
    {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))}
    {P E : (Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2) → ℝ}
    (hlocal : 1 < ActiveEdge.localOrder ell)
    (hcert : HasNSCertificateDegreeLE
      (Preprocess.cleaningFormula hell) P proofDegree)
    (hidentity : ∀ z, P z = 1 + JR.eval z + E z)
    (herror : ErrorControlled E)
    (hHard : SoPL.PathFamilyNSHardness ell hell degreeLowerBound)
    (htransferDegree : 2 * proofDegree * (7 * ell) < degreeLowerBound)
    (hNonnegative : JR.Nonnegative)
    (hJuntaDegree : JR.DegreeLE juntaDegree)
    (hAlign : JR.NodeAligned) (hCurious : JR.ExitCurious hell)
    (hNonWitness : JR.NonWitnessing (Preprocess.cleaningFormula hell))
    (hsmall : 100 * juntaDegree ≤ ActiveEdge.localOrder ell) :
    ∃ state, GoodState hell JR state ∧
      state.stage = ActiveEdge.localOrder ell - 1 ∧
        (7 / 5 : ℝ) ^ (ActiveEdge.localOrder ell - 1) ≤ state.B := by
  apply amplification_iterate hlocal hcert hidentity herror hHard
    htransferDegree hNonnegative hJuntaDegree hAlign hCurious hNonWitness
      hsmall (ActiveEdge.localOrder ell - 1)
  omega

end Amplification

end SoD

end Revres
