import Revres.DecisionTree.SearchCNF
import Revres.Encoding.BinaryPointer
import Revres.SoPL.Semantics
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Binary encoding and local search CNF for successor--predecessor labellings

The two pointer blocks of a grid node are stored consecutively.  The local
verifier follows at most two pointers to test activity and at most two more
to test whether a node is a proper sink.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace Encoding

abbrev order (ell : Nat) : Nat := BinaryPointer.order ell

abbrev Node (ell : Nat) := GridNode (order ell)

def variableCount (ell : Nat) : Nat :=
  (order ell * order ell) * (2 * ell)

def bitIndexEquiv (ell : Nat) :
    (Node ell × (Fin 2 × Fin ell)) ≃ Fin (variableCount ell) :=
  (Equiv.prodCongr
      (finProdFinEquiv (m := order ell) (n := order ell))
      (finProdFinEquiv (m := 2) (n := ell))).trans
    (finProdFinEquiv (m := order ell * order ell) (n := 2 * ell))

def successorBit (ell : Nat) (u : Node ell) (b : Fin ell) :
    Fin (variableCount ell) :=
  bitIndexEquiv ell (u, (0, b))

def predecessorBit (ell : Nat) (u : Node ell) (b : Fin ell) :
    Fin (variableCount ell) :=
  bitIndexEquiv ell (u, (1, b))

noncomputable def decodeInput (ell : Nat) (x : Fin (variableCount ell) → F2) :
    SoPL.Input (order ell) where
  successor u := BinaryPointer.decode (fun b => x (successorBit ell u b))
  predecessor u := BinaryPointer.decode (fun b => x (predecessorBit ell u b))

@[simp] theorem decodeInput_successor (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (decodeInput ell x).successor u =
      BinaryPointer.decode (fun b => x (successorBit ell u b)) :=
  rfl

@[simp] theorem decodeInput_predecessor (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (decodeInput ell x).predecessor u =
      BinaryPointer.decode (fun b => x (predecessorBit ell u b)) :=
  rfl

noncomputable def encodeInput (ell : Nat) (s : SoPL.Input (order ell)) :
    Fin (variableCount ell) → F2 := fun i =>
  let index := (bitIndexEquiv ell).symm i
  if index.2.1 = 0 then
    BinaryPointer.encode (s.successor index.1) index.2.2
  else
    BinaryPointer.encode (s.predecessor index.1) index.2.2

@[simp] theorem encodeInput_successorBit (ell : Nat) (s : SoPL.Input (order ell))
    (u : Node ell) (b : Fin ell) :
    encodeInput ell s (successorBit ell u b) =
      BinaryPointer.encode (s.successor u) b := by
  simp [encodeInput, successorBit]

@[simp] theorem encodeInput_predecessorBit (ell : Nat) (s : SoPL.Input (order ell))
    (u : Node ell) (b : Fin ell) :
    encodeInput ell s (predecessorBit ell u b) =
      BinaryPointer.encode (s.predecessor u) b := by
  simp [encodeInput, predecessorBit]

@[simp] theorem decodeInput_encodeInput (ell : Nat) (s : SoPL.Input (order ell)) :
    decodeInput ell (encodeInput ell s) = s := by
  apply SoPL.Input.ext
  · funext u
    simp [decodeInput]
  · funext u
    simp [decodeInput]

@[simp] theorem encodeInput_decodeInput (ell : Nat)
    (x : Fin (variableCount ell) → F2) :
    encodeInput ell (decodeInput ell x) = x := by
  funext i
  let index := (bitIndexEquiv ell).symm i
  by_cases hkind : index.2.1 = 0
  · simp only [encodeInput, index, hkind, if_pos]
    change BinaryPointer.encode
        (BinaryPointer.decode (fun b => x (successorBit ell index.1 b))) index.2.2 = x i
    rw [congrFun (BinaryPointer.encode_decode
      (bits := fun b => x (successorBit ell index.1 b))) index.2.2]
    have hi : successorBit ell index.1 index.2.2 = i := by
      have htuple : (index.1, (0, index.2.2)) = index := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hkind.symm
          · rfl
      calc
        successorBit ell index.1 index.2.2 = (bitIndexEquiv ell) index := by
          rw [successorBit, htuple]
        _ = i := (bitIndexEquiv ell).apply_symm_apply i
    rw [hi]
  · have hone : index.2.1 = 1 := by
      have hval : index.2.1.val = 0 ∨ index.2.1.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp
          (Nat.le_of_lt_succ index.2.1.isLt)
      rcases hval with hzero | hone
      · exact (hkind (Fin.eq_of_val_eq hzero)).elim
      · exact Fin.eq_of_val_eq hone
    simp only [encodeInput, index, hkind]
    change BinaryPointer.encode
        (BinaryPointer.decode (fun b => x (predecessorBit ell index.1 b))) index.2.2 = x i
    rw [congrFun (BinaryPointer.encode_decode
      (bits := fun b => x (predecessorBit ell index.1 b))) index.2.2]
    have hi : predecessorBit ell index.1 index.2.2 = i := by
      have htuple : (index.1, (1, index.2.2)) = index := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hone.symm
          · rfl
      calc
        predecessorBit ell index.1 index.2.2 = (bitIndexEquiv ell) index := by
          rw [predecessorBit, htuple]
        _ = i := (bitIndexEquiv ell).apply_symm_apply i
    rw [hi]

noncomputable def inputEquiv (ell : Nat) :
    (Fin (variableCount ell) → F2) ≃ SoPL.Input (order ell) where
  toFun := decodeInput ell
  invFun := encodeInput ell
  left_inv := encodeInput_decodeInput ell
  right_inv := decodeInput_encodeInput ell

noncomputable def readSuccessor (ell : Nat) (u : Node ell) :
    DecisionTree (variableCount ell) (Option (Fin (order ell))) :=
  BinaryPointer.read (successorBit ell u)

noncomputable def readPredecessor (ell : Nat) (u : Node ell) :
    DecisionTree (variableCount ell) (Option (Fin (order ell))) :=
  BinaryPointer.read (predecessorBit ell u)

@[simp] theorem eval_readSuccessor (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (readSuccessor ell u).eval x = (decodeInput ell x).successor u := by
  simp [readSuccessor, decodeInput]

@[simp] theorem eval_readPredecessor (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (readPredecessor ell u).eval x = (decodeInput ell x).predecessor u := by
  simp [readPredecessor, decodeInput]

@[simp] theorem depth_readSuccessor (ell : Nat) (u : Node ell) :
    (readSuccessor ell u).depth = ell := by
  simp [readSuccessor]

@[simp] theorem depth_readPredecessor (ell : Nat) (u : Node ell) :
    (readPredecessor ell u).depth = ell := by
  simp [readPredecessor]

private noncomputable def activeTree (ell : Nat) (u : Node ell) :
    DecisionTree (variableCount ell) Bool :=
  if hu : u.IsInternal then
    (readSuccessor ell u).bind fun successor =>
      match successor with
      | none => .leaf false
      | some column =>
          (readPredecessor ell (u.next hu column)).map fun predecessor =>
            decide (predecessor = some u.column)
  else
    (readSuccessor ell u).map fun successor => decide (successor ≠ none)

private theorem active_iff_of_internal_successor_eq_some
    {ell : Nat} (s : SoPL.Input (order ell)) (u : Node ell)
    (hu : u.IsInternal) (column : Fin (order ell))
    (hs : s.successor u = some column) :
    s.Active u ↔ s.predecessor (u.next hu column) = some u.column := by
  constructor
  · intro hactive
    obtain ⟨v, hedge⟩ := (s.active_internal_iff hu).mp hactive
    have hcolumn : v.column = column := by
      exact Option.some.inj (hedge.2.1.symm.trans hs)
    have hv : u.next hu column = v := by
      rw [← hcolumn]
      exact GridNode.eq_next_of_nextRow hedge.1
    rw [hv]
    exact hedge.2.2
  · intro hp
    apply (s.active_internal_iff hu).mpr
    exact ⟨u.next hu column, u.nextRow_next hu column, hs, hp⟩

private theorem not_active_of_internal_successor_eq_none
    {ell : Nat} (s : SoPL.Input (order ell)) (u : Node ell)
    (hu : u.IsInternal) (hs : s.successor u = none) :
    ¬s.Active u := by
  intro hactive
  obtain ⟨v, hedge⟩ := (s.active_internal_iff hu).mp hactive
  rw [SoPL.Input.ActiveEdge, hs] at hedge
  simp at hedge

private theorem activeTree_correct (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (activeTree ell u).eval x = true ↔ (decodeInput ell x).Active u := by
  let s := decodeInput ell x
  by_cases hu : u.IsInternal
  · cases hs : s.successor u with
    | none =>
        have hnot := not_active_of_internal_successor_eq_none s u hu hs
        have hsbits :
            BinaryPointer.decode (fun b => x (successorBit ell u b)) = none := by
          simpa [s] using hs
        simp [activeTree, hu, hsbits, s, hnot]
    | some column =>
        have hiff := active_iff_of_internal_successor_eq_some s u hu column hs
        have hsbits :
            BinaryPointer.decode (fun b => x (successorBit ell u b)) = some column := by
          simpa [s] using hs
        simp [activeTree, hu, hsbits, s, hiff]
  · have hlast : u.IsLastRow := (u.internal_or_last.resolve_left hu)
    rw [activeTree, dif_neg hu, DecisionTree.eval_map, eval_readSuccessor]
    simp only [decide_eq_true_eq]
    exact ((decodeInput ell x).active_lastRow_iff hlast).symm

private theorem activeTree_false_correct (ell : Nat)
    (x : Fin (variableCount ell) → F2) (u : Node ell) :
    (activeTree ell u).eval x = false ↔ ¬(decodeInput ell x).Active u := by
  constructor
  · intro hfalse hactive
    have htrue := (activeTree_correct ell x u).mpr hactive
    rw [hfalse] at htrue
    cases htrue
  · intro hnot
    cases hvalue : (activeTree ell u).eval x
    · rfl
    · exact (hnot ((activeTree_correct ell x u).mp hvalue)).elim

private theorem activeTree_depth_le (ell : Nat) (u : Node ell) :
    (activeTree ell u).depth ≤ 2 * ell := by
  by_cases hu : u.IsInternal
  · let next := fun successor : Option (Fin (order ell)) =>
      match successor with
      | none => DecisionTree.leaf false
      | some column =>
          (readPredecessor ell (u.next hu column)).map fun predecessor =>
            decide (predecessor = some u.column)
    have hnext : ∀ successor, (next successor).depth ≤ ell := by
      intro successor
      cases successor <;> simp [next]
    have hbind := DecisionTree.depth_bind_le (readSuccessor ell u) next hnext
    simpa [activeTree, hu, next, two_mul] using hbind
  · simp [activeTree, hu, two_mul]

def previous {ell : Nat} (v : Node ell) (_hv : ¬v.IsFirstRow)
    (column : Fin (order ell)) : Node ell :=
  (⟨v.row.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) v.row.isLt⟩, column)

theorem previous_nextRow {ell : Nat} (v : Node ell) (hv : ¬v.IsFirstRow)
    (column : Fin (order ell)) : (previous v hv column).NextRow v := by
  have hne : v.row.val ≠ 0 := by
    intro hzero
    exact hv hzero
  change v.row.val = v.row.val - 1 + 1
  exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)).symm

private theorem eq_previous_of_nextRow {ell : Nat} {u v : Node ell}
    (hv : ¬v.IsFirstRow) (hrow : u.NextRow v) :
    u = previous v hv u.column := by
  apply Prod.ext
  · apply Fin.ext
    change u.row.val = v.row.val - 1
    rw [hrow]
    simp
  · rfl

private theorem exists_activeEdge_iff_of_predecessor_eq_some
    {ell : Nat} (s : SoPL.Input (order ell)) (v : Node ell)
    (hv : ¬v.IsFirstRow) (column : Fin (order ell))
    (hp : s.predecessor v = some column) :
    (∃ u, s.ActiveEdge u v) ↔
      s.successor (previous v hv column) = some v.column := by
  constructor
  · rintro ⟨u, hedge⟩
    have hcolumn : u.column = column := by
      exact Option.some.inj (hedge.2.2.symm.trans hp)
    have hu : u = previous v hv column := by
      calc
        u = previous v hv u.column := eq_previous_of_nextRow hv hedge.1
        _ = previous v hv column := by rw [hcolumn]
    rw [← hu]
    exact hedge.2.1
  · intro hs
    exact ⟨previous v hv column, previous_nextRow v hv column, hs, hp⟩

private theorem no_incoming_edge_of_firstRow
    {ell : Nat} (s : SoPL.Input (order ell)) (v : Node ell)
    (hv : v.IsFirstRow) : ¬∃ u, s.ActiveEdge u v := by
  rintro ⟨u, hedge⟩
  have hne : v.row.val ≠ 0 := by
    rw [hedge.1]
    exact Nat.add_one_ne_zero u.row.val
  exact hne hv

private theorem no_incoming_edge_of_predecessor_eq_none
    {ell : Nat} (s : SoPL.Input (order ell)) (v : Node ell)
    (hp : s.predecessor v = none) : ¬∃ u, s.ActiveEdge u v := by
  rintro ⟨u, hedge⟩
  rw [SoPL.Input.ActiveEdge, hp] at hedge
  simp at hedge

private noncomputable def incomingTree (ell : Nat) (v : Node ell) :
    DecisionTree (variableCount ell) Bool :=
  if hv : v.IsFirstRow then
    .leaf false
  else
    (readPredecessor ell v).bind fun predecessor =>
      match predecessor with
      | none => .leaf false
      | some column =>
          (readSuccessor ell (previous v hv column)).map fun successor =>
            decide (successor = some v.column)

private theorem incomingTree_correct (ell : Nat)
    (x : Fin (variableCount ell) → F2) (v : Node ell) :
    (incomingTree ell v).eval x = true ↔
      ∃ u, (decodeInput ell x).ActiveEdge u v := by
  let s := decodeInput ell x
  by_cases hv : v.IsFirstRow
  · have hnot := no_incoming_edge_of_firstRow s v hv
    simp only [incomingTree, dif_pos hv, DecisionTree.eval_leaf]
    constructor
    · intro h
      cases h
    · intro h
      exact (hnot (by simpa [s] using h)).elim
  · cases hp : s.predecessor v with
    | none =>
        have hnot := no_incoming_edge_of_predecessor_eq_none s v hp
        have hpbits :
            BinaryPointer.decode (fun b => x (predecessorBit ell v b)) = none := by
          simpa [s] using hp
        simp [incomingTree, hv, hpbits, s, hnot]
    | some column =>
        have hiff :=
          exists_activeEdge_iff_of_predecessor_eq_some s v hv column hp
        have hpbits :
            BinaryPointer.decode (fun b => x (predecessorBit ell v b)) = some column := by
          simpa [s] using hp
        simp [incomingTree, hv, hpbits, s, hiff]

private theorem incomingTree_false_correct (ell : Nat)
    (x : Fin (variableCount ell) → F2) (v : Node ell) :
    (incomingTree ell v).eval x = false ↔
      ¬∃ u, (decodeInput ell x).ActiveEdge u v := by
  constructor
  · intro hfalse hincoming
    have htrue := (incomingTree_correct ell x v).mpr hincoming
    rw [hfalse] at htrue
    cases htrue
  · intro hnot
    cases hvalue : (incomingTree ell v).eval x
    · rfl
    · exact (hnot ((incomingTree_correct ell x v).mp hvalue)).elim

private theorem incomingTree_depth_le (ell : Nat) (v : Node ell) :
    (incomingTree ell v).depth ≤ 2 * ell := by
  by_cases hv : v.IsFirstRow
  · simp [incomingTree, hv]
  · let next := fun predecessor : Option (Fin (order ell)) =>
      match predecessor with
      | none => DecisionTree.leaf false
      | some column =>
          (readSuccessor ell (previous v hv column)).map fun successor =>
            decide (successor = some v.column)
    have hnext : ∀ predecessor, (next predecessor).depth ≤ ell := by
      intro predecessor
      cases predecessor <;> simp [next]
    have hbind := DecisionTree.depth_bind_le (readPredecessor ell v) next hnext
    simpa [incomingTree, hv, next, two_mul] using hbind

noncomputable def verifier (ell : Nat) (hell : 0 < ell) : SoPL.Output (order ell) →
    DecisionTree (variableCount ell) Bool
  | .inactiveSource =>
      (activeTree ell (GridNode.distinguished (BinaryPointer.order_pos hell))).map
        fun active => !active
  | .activeLast u =>
      if u.IsLastRow then activeTree ell u else .leaf false
  | .properSink v =>
      (incomingTree ell v).bind fun incoming =>
        if incoming then (activeTree ell v).map fun active => !active
        else .leaf false

theorem verifier_correct (ell : Nat) (hell : 0 < ell)
    (x : Fin (variableCount ell) → F2) (o : SoPL.Output (order ell)) :
    (verifier ell hell o).eval x = true ↔
      SoPL.Valid (BinaryPointer.order_pos hell) (decodeInput ell x) o := by
  cases o with
  | inactiveSource =>
      simp [verifier, activeTree_false_correct, SoPL.Valid]
  | activeLast u =>
      by_cases hlast : u.IsLastRow
      · simp [verifier, hlast, activeTree_correct, SoPL.Valid]
      · simp [verifier, hlast, SoPL.Valid]
  | properSink v =>
      let s := decodeInput ell x
      by_cases hincoming : ∃ u, s.ActiveEdge u v
      · have heval : (incomingTree ell v).eval x = true :=
          (incomingTree_correct ell x v).mpr (by simpa [s] using hincoming)
        simp [verifier, heval, activeTree_false_correct, SoPL.Valid,
          SoPL.Input.ProperSink, s, hincoming]
      · have heval : (incomingTree ell v).eval x = false :=
          (incomingTree_false_correct ell x v).mpr (by simpa [s] using hincoming)
        simp [verifier, heval, SoPL.Valid, SoPL.Input.ProperSink, s, hincoming]

theorem verifier_depth_le (ell : Nat) (hell : 0 < ell)
    (o : SoPL.Output (order ell)) :
    (verifier ell hell o).depth ≤ 4 * ell := by
  cases o with
  | inactiveSource =>
      calc
        (verifier ell hell .inactiveSource).depth =
            (activeTree ell (GridNode.distinguished
              (BinaryPointer.order_pos hell))).depth := by simp [verifier]
        _ ≤ 2 * ell := activeTree_depth_le ell _
        _ ≤ 4 * ell := by omega
  | activeLast u =>
      by_cases hlast : u.IsLastRow
      · calc
          (verifier ell hell (.activeLast u)).depth = (activeTree ell u).depth := by
            simp [verifier, hlast]
          _ ≤ 2 * ell := activeTree_depth_le ell u
          _ ≤ 4 * ell := by omega
      · simp [verifier, hlast]
  | properSink v =>
      let next := fun incoming : Bool =>
        if incoming then (activeTree ell v).map fun active => !active
        else DecisionTree.leaf false
      have hnext : ∀ incoming, (next incoming).depth ≤ 2 * ell := by
        intro incoming
        cases incoming <;> simp [next, activeTree_depth_le]
      have hbind := DecisionTree.depth_bind_le (incomingTree ell v) next hnext
      calc
        (verifier ell hell (.properSink v)).depth ≤
            (incomingTree ell v).depth + 2 * ell := by
          simpa [verifier, next] using hbind
        _ ≤ 2 * ell + 2 * ell :=
          Nat.add_le_add_right (incomingTree_depth_le ell v) (2 * ell)
        _ = 4 * ell := by omega

noncomputable def searchProblem (ell : Nat) (hell : 0 < ell) :
    SearchProblem (variableCount ell) where
  Output := SoPL.Output (order ell)
  instOutputFintype := inferInstance
  valid := fun x o => SoPL.Valid (BinaryPointer.order_pos hell) (decodeInput ell x) o
  total := fun x => SoPL.total (BinaryPointer.order_pos hell) (decodeInput ell x)
  verifier := verifier ell hell
  verifier_correct := verifier_correct ell hell

theorem searchProblem_verifierDepth_le (ell : Nat) (hell : 0 < ell) :
    (searchProblem ell hell).verifierDepth ≤ 4 * ell := by
  classical
  rw [SearchProblem.verifierDepth]
  exact Finset.sup_le fun o _ho => verifier_depth_le ell hell o

noncomputable def searchCNF (ell : Nat) (hell : 0 < ell) : CNF (variableCount ell) :=
  (searchProblem ell hell).toCNF

noncomputable def clauseOutput {ell : Nat} {hell : 0 < ell}
    (C : ↑(searchCNF ell hell)) : SoPL.Output (order ell) :=
  (searchProblem ell hell).clauseOutput C

theorem clauseOutput_mem {ell : Nat} {hell : 0 < ell}
    (C : ↑(searchCNF ell hell)) :
    C.1 ∈ (searchProblem ell hell).outputClauses (clauseOutput C) :=
  (searchProblem ell hell).clauseOutput_mem C

theorem clauseOutput_valid {ell : Nat} {hell : 0 < ell}
    (C : ↑(searchCNF ell hell)) {x : Fin (variableCount ell) → F2}
    (hC : C.1.Falsified x) :
    SoPL.Valid (BinaryPointer.order_pos hell) (decodeInput ell x) (clauseOutput C) :=
  (searchProblem ell hell).clauseOutput_valid C hC

theorem searchCNF_unsat (ell : Nat) (hell : 0 < ell) :
    (searchCNF ell hell).Unsat :=
  (searchProblem ell hell).toCNF_unsat

theorem searchCNF_width_le (ell : Nat) (hell : 0 < ell) :
    (searchCNF ell hell).width ≤ 4 * ell :=
  (searchProblem ell hell).toCNF_width_le_verifierDepth.trans
    (searchProblem_verifierDepth_le ell hell)

theorem inactiveSource_clauses_falsified_iff
    {ell : Nat} (hell : 0 < ell) (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses .inactiveSource,
        C.Falsified x) ↔
      ¬(decodeInput ell x).Active
        (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  simpa [searchProblem, SoPL.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.inactiveSource) x)

theorem activeLast_clauses_falsified_iff
    {ell : Nat} (hell : 0 < ell) (u : Node ell)
    (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses (.activeLast u),
        C.Falsified x) ↔
      u.IsLastRow ∧ (decodeInput ell x).Active u := by
  simpa [searchProblem, SoPL.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.activeLast u) x)

theorem properSink_clauses_falsified_iff
    {ell : Nat} (hell : 0 < ell) (v : Node ell)
    (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses (.properSink v),
        C.Falsified x) ↔
      (decodeInput ell x).ProperSink v := by
  simpa [searchProblem, SoPL.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.properSink v) x)

end Encoding

end SoPL

end Revres
