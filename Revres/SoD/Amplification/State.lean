import Revres.Conical.Representation
import Revres.SoD.ActiveEdge

/-!
# Amplification states

This module defines restrictions and the invariant carried between amplification
stages.  The mutable state stores only independent data; its decoded null input
and embedded geometry are derived canonically.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Amplification

open scoped BigOperators

variable {ell : ℕ}

/-- Encoded successor coordinates belonging to one embedded macrobox. -/
def boxBits (hell : 0 < ell) (Q : GridNode (ActiveEdge.localOrder ell)) :
    Finset (Fin (Encoding.variableCount (2 * ell))) :=
  (ActiveEdge.embeddedSubgrid hell Q).biUnion (Encoding.nodeBits (2 * ell))

theorem mem_boxBits_iff {hell : 0 < ell}
    {Q : GridNode (ActiveEdge.localOrder ell)}
    {i : Fin (Encoding.variableCount (2 * ell))} :
    i ∈ boxBits hell Q ↔
      Encoding.nodeOfBit (2 * ell) i ∈ ActiveEdge.embeddedSubgrid hell Q := by
  constructor
  · intro hi
    rw [boxBits, Finset.mem_biUnion] at hi
    obtain ⟨v, hv, hiv⟩ := hi
    have hnode : Encoding.nodeOfBit (2 * ell) i = v :=
      Encoding.mem_nodeBits_iff.mp hiv
    simpa [hnode] using hv
  · intro hi
    rw [boxBits, Finset.mem_biUnion]
    exact ⟨Encoding.nodeOfBit (2 * ell) i, hi,
      Encoding.mem_nodeBits_iff.mpr rfl⟩

theorem successorBit_mem_boxBits (hell : 0 < ell)
    (Q u : GridNode (ActiveEdge.localOrder ell)) (b : Fin (2 * ell)) :
    Encoding.successorBit (ActiveEdge.embedNode hell Q u) b ∈ boxBits hell Q := by
  rw [mem_boxBits_iff, Encoding.nodeOfBit_successorBit]
  exact ActiveEdge.mem_embeddedSubgrid_iff.mpr ⟨u, rfl⟩

theorem not_mem_boxBits_of_node_not_mem {hell : 0 < ell}
    {Q : GridNode (ActiveEdge.localOrder ell)}
    {i : Fin (Encoding.variableCount (2 * ell))}
    (hi : Encoding.nodeOfBit (2 * ell) i ∉ ActiveEdge.embeddedSubgrid hell Q) :
    i ∉ boxBits hell Q := by
  intro himem
  exact hi (mem_boxBits_iff.mp himem)

theorem boxBits_disjoint {hell : 0 < ell}
    {Q R : GridNode (ActiveEdge.localOrder ell)} (hQR : Q ≠ R) :
    Disjoint (boxBits hell Q) (boxBits hell R) := by
  rw [Finset.disjoint_left]
  intro i hiQ hiR
  have hnodes := ActiveEdge.embeddedSubgrid_disjoint (hell := hell) hQR
  exact (Finset.disjoint_left.mp hnodes)
    (mem_boxBits_iff.mp hiQ) (mem_boxBits_iff.mp hiR)

@[simp]
theorem card_boxBits (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell)) :
    (boxBits hell Q).card = (ActiveEdge.localOrder ell) ^ 2 * (2 * ell) := by
  have hpairwise :
      (↑(ActiveEdge.embeddedSubgrid hell Q) :
        Set (GridNode (ActiveEdge.ambientOrder ell))).PairwiseDisjoint
        (Encoding.nodeBits (2 * ell)) := by
    intro u _hu v _hv huv
    exact Encoding.nodeBits_disjoint huv
  rw [boxBits, Finset.card_biUnion hpairwise]
  simp only [Encoding.card_nodeBits, Finset.sum_const, nsmul_eq_mul]
  rw [ActiveEdge.card_embeddedSubgrid]
  simp [pow_two]

/-- A restriction is the canonical partial assignment already used for terms. -/
abbrev Restriction (ell : ℕ) := Term (Encoding.variableCount (2 * ell))

namespace Restriction

/-- The unset coordinates of `rho` are exactly `S`. -/
def FreeExactly (rho : Restriction ell)
    (S : Finset (Fin (Encoding.variableCount (2 * ell)))) : Prop :=
  ∀ i, rho.val i = none ↔ i ∈ S

theorem freeExactly_iff {rho : Restriction ell}
    {S : Finset (Fin (Encoding.variableCount (2 * ell)))} :
    rho.FreeExactly S ↔ ∀ i, rho.val i = none ↔ i ∈ S :=
  Iff.rfl

/-- Fill every free coordinate by the null bit zero. -/
def nullAssignment (rho : Restriction ell) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  rho.completion

/-- Decode the zero-filled restriction as an ambient SoD input. -/
noncomputable def nullInput (rho : Restriction ell) :
    SoD.Input (ActiveEdge.ambientOrder ell) :=
  Encoding.decodeInput rho.nullAssignment

theorem matches_nullAssignment (rho : Restriction ell) :
    rho.Matches rho.nullAssignment := by
  intro i b hib
  simp [nullAssignment, Term.completion, hib]

theorem nullAssignment_eq_of_eq_some {rho : Restriction ell}
    {i : Fin (Encoding.variableCount (2 * ell))} {b : Lemma53.F2}
    (hi : rho.val i = some b) : rho.nullAssignment i = b := by
  simp [nullAssignment, Term.completion, hi]

theorem matches_of_eq_nullAssignment_on_fixed {rho : Restriction ell}
    {z : Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2}
    (hfixed : ∀ i b, rho.val i = some b → z i = rho.nullAssignment i) :
    rho.Matches z := by
  intro i b hi
  exact (hfixed i b hi).trans (nullAssignment_eq_of_eq_some hi)

@[simp]
theorem encodeInput_nullInput (rho : Restriction ell) :
    Encoding.encodeInput rho.nullInput = rho.nullAssignment := by
  simp [nullInput]

theorem nullInput_successor_eq_none {hell : 0 < ell}
    {rho : Restriction ell} {Q : GridNode (ActiveEdge.localOrder ell)}
    (hfree : rho.FreeExactly (boxBits hell Q))
    (u : GridNode (ActiveEdge.localOrder ell)) :
    rho.nullInput.successor (ActiveEdge.embedNode hell Q u) = none := by
  rw [nullInput, Encoding.decodeInput_successor, BinaryPointer.decode_eq_none_iff]
  funext b
  have hnone :
      rho.val (Encoding.successorBit (ActiveEdge.embedNode hell Q u) b) = none :=
    (hfree _).mpr (successorBit_mem_boxBits hell Q u b)
  simp [nullAssignment, Term.completion, BinaryPointer.nullBits, hnone]

end Restriction

/-- Every successor record in `Q` is null. -/
def NullOnBox (hell : 0 < ell) (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (Q : GridNode (ActiveEdge.localOrder ell)) : Prop :=
  ∀ u, x.successor (ActiveEdge.embedNode hell Q u) = none

/-- Every macrobox in a strictly later macro-row is null. -/
def NullAfter (hell : 0 < ell) (x : SoD.Input (ActiveEdge.ambientOrder ell))
    (Q : GridNode (ActiveEdge.localOrder ell)) : Prop :=
  ∀ R, Q.row.val < R.row.val → NullOnBox hell x R

/-- Independent mutable data for one amplification stage. -/
structure AmpState (ell : ℕ) where
  stage : ℕ
  restriction : Restriction ell
  currentBox : GridNode (ActiveEdge.localOrder ell)
  B : ℝ

namespace AmpState

def currentSubgrid (s : AmpState ell) (hell : 0 < ell) :
    Finset (GridNode (ActiveEdge.ambientOrder ell)) :=
  ActiveEdge.embeddedSubgrid hell s.currentBox

def currentCorner (s : AmpState ell) (hell : 0 < ell) :
    GridNode (ActiveEdge.ambientOrder ell) :=
  ActiveEdge.embeddedCorner hell s.currentBox

def nullAssignment (s : AmpState ell) :
    Fin (Encoding.variableCount (2 * ell)) → Lemma53.F2 :=
  s.restriction.nullAssignment

noncomputable def nullInput (s : AmpState ell) :
    SoD.Input (ActiveEdge.ambientOrder ell) :=
  s.restriction.nullInput

end AmpState

/-- The exact structural content of a good restriction. -/
structure StructuralInvariant (hell : 0 < ell) (s : AmpState ell) : Prop where
  free_current : s.restriction.FreeExactly (boxBits hell s.currentBox)
  later_null : NullAfter hell s.nullInput s.currentBox
  solution_control :
    ∀ o, SoD.Valid (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
        s.nullInput o →
      match o with
      | .inactiveSource =>
          s.currentCorner hell =
            GridNode.distinguished
              (BinaryPointer.order_pos (ActiveEdge.ambientWidth_pos hell))
      | .activeLast _ => False
      | .properSink u =>
          u ∉ s.currentSubgrid hell ∧
            s.nullInput.PointsTo u (s.currentCorner hell)

namespace StructuralInvariant

theorem current_null {hell : 0 < ell} {s : AmpState ell}
    (h : StructuralInvariant hell s) :
    NullOnBox hell s.nullInput s.currentBox := by
  intro u
  exact Restriction.nullInput_successor_eq_none h.free_current u

theorem currentCorner_inactive {hell : 0 < ell} {s : AmpState ell}
    (h : StructuralInvariant hell s) :
    s.nullInput.successor (s.currentCorner hell) = none := by
  exact h.current_null (GridNode.distinguished (BinaryPointer.order_pos hell))

end StructuralInvariant

/-- The lower bound holds uniformly over every completion of the restriction. -/
def NumericalInvariant (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (s : AmpState ell) : Prop :=
  ∀ z, s.restriction.Matches z → s.B ≤ 1 + JR.eval z

/-- A structurally and numerically good amplification state. -/
structure GoodState (hell : 0 < ell)
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (s : AmpState ell) : Prop where
  stage_lt : s.stage < ActiveEdge.localOrder ell
  row_eq_stage : s.currentBox.row.val = s.stage
  current_candidate :
    s.currentBox.column ≠ SoD.parkingColumn (BinaryPointer.order_pos hell)
  one_le_B : 1 ≤ s.B
  structural : StructuralInvariant hell s
  numerical : NumericalInvariant JR s

/-- The manuscript's first macrobox, with zero-based coordinates `(0, 0)`. -/
def initialBox (hell : 0 < ell) : GridNode (ActiveEdge.localOrder ell) :=
  GridNode.distinguished (BinaryPointer.order_pos hell)

/-- Free the initial macrobox and fix every other ambient bit to zero. -/
def baseRestriction (hell : 0 < ell) : Restriction ell where
  val i := if i ∈ boxBits hell (initialBox hell) then none else some 0

/-- Initial amplification state with lower bound one. -/
def baseState (hell : 0 < ell) : AmpState ell where
  stage := 0
  restriction := baseRestriction hell
  currentBox := initialBox hell
  B := 1

theorem baseRestriction_freeExactly (hell : 0 < ell) :
    (baseRestriction hell).FreeExactly (boxBits hell (initialBox hell)) := by
  intro i
  simp [baseRestriction]

theorem baseRestriction_nullAssignment (hell : 0 < ell) :
    (baseRestriction hell).nullAssignment = fun _ => 0 := by
  funext i
  by_cases hi : i ∈ boxBits hell (initialBox hell) <;>
    simp [Restriction.nullAssignment, Term.completion, baseRestriction, hi]

theorem baseRestriction_nullInput_successor_eq_none (hell : 0 < ell)
    (u : GridNode (ActiveEdge.ambientOrder ell)) :
    (baseRestriction hell).nullInput.successor u = none := by
  rw [Restriction.nullInput, Encoding.decodeInput_successor,
    BinaryPointer.decode_eq_none_iff]
  funext b
  rw [baseRestriction_nullAssignment]
  rfl

theorem good_baseState (hell : 0 < ell)
    (hlocal : 1 < ActiveEdge.localOrder ell)
    (JR : JuntaRep (Encoding.variableCount (2 * ell)))
    (hJR : JR.Nonnegative) :
    GoodState hell JR (baseState hell) := by
  constructor
  · simpa [baseState] using BinaryPointer.order_pos hell
  · rfl
  · intro hcolumn
    have hval : (0 : ℕ) = ActiveEdge.localOrder ell - 1 :=
      congrArg Fin.val hcolumn
    omega
  · simp [baseState]
  · constructor
    · exact baseRestriction_freeExactly hell
    · intro R _hrow u
      exact baseRestriction_nullInput_successor_eq_none hell _
    · intro o hvalid
      cases o with
      | inactiveSource =>
          exact ActiveEdge.distinguished_embeddedCorner hell
      | activeLast u =>
          have hnone := baseRestriction_nullInput_successor_eq_none hell u
          exact hvalid.2 hnone
      | properSink u =>
          obtain ⟨v, hpoints, _hinactive⟩ := hvalid
          have hnone : (baseState hell).nullInput.successor u = none := by
            simpa [AmpState.nullInput, baseState] using
              baseRestriction_nullInput_successor_eq_none hell u
          have hsome := hpoints.2
          rw [hnone] at hsome
          simp at hsome
  · intro z _hz
    have hnonneg := JuntaRep.eval_nonneg hJR z
    change (1 : ℝ) ≤ 1 + JR.eval z
    linarith

/-- The parking macrobox in the row immediately following `Q`. -/
def parkingExitBox (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell)) (hQ : Q.IsInternal) :
    GridNode (ActiveEdge.localOrder ell) :=
  SoD.parkingBox (BinaryPointer.order_pos hell) (SoD.nextMacroRowIndex Q hQ)

theorem parkingExitBox_nextRow (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell)) (hQ : Q.IsInternal) :
    Q.NextRow (parkingExitBox hell Q hQ) := by
  rfl

@[simp]
theorem parkingExitBox_column (hell : 0 < ell)
    (Q : GridNode (ActiveEdge.localOrder ell)) (hQ : Q.IsInternal) :
    (parkingExitBox hell Q hQ).column =
      SoD.parkingColumn (BinaryPointer.order_pos hell) :=
  rfl

namespace GoodState

/-- A good nonterminal state supplies the exact base context for active-edge replacement. -/
noncomputable def toStageContext {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal) :
    ActiveEdge.StageContext ell hell where
  currentBox := s.currentBox
  current_internal := hinternal
  current_candidate := hgood.current_candidate
  exitBox := parkingExitBox hell s.currentBox hinternal
  exit_nextRow := parkingExitBox_nextRow hell s.currentBox hinternal
  base := s.nullInput
  base_null_current := hgood.structural.current_null
  exit_inactive := by
    intro hactive
    apply hactive
    exact hgood.structural.later_null _
      (by
        have hnext := parkingExitBox_nextRow hell s.currentBox hinternal
        rw [hnext]
        exact Nat.lt_succ_self _)
      (GridNode.distinguished (BinaryPointer.order_pos hell))
  base_solution_control := hgood.structural.solution_control

@[simp]
theorem toStageContext_currentBox {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal) :
    (hgood.toStageContext hinternal).currentBox = s.currentBox :=
  rfl

@[simp]
theorem toStageContext_exitBox {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal) :
    (hgood.toStageContext hinternal).exitBox =
      parkingExitBox hell s.currentBox hinternal :=
  rfl

@[simp]
theorem toStageContext_base {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal) :
    (hgood.toStageContext hinternal).base = s.nullInput :=
  rfl

@[simp]
theorem toStageContext_corner {hell : 0 < ell}
    {JR : JuntaRep (Encoding.variableCount (2 * ell))} {s : AmpState ell}
    (hgood : GoodState hell JR s) (hinternal : s.currentBox.IsInternal) :
    ActiveEdge.embeddedCorner hell (hgood.toStageContext hinternal).currentBox =
      s.currentCorner hell :=
  rfl

end GoodState

end Amplification

end SoD

end Revres
