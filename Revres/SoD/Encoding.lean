import Revres.DecisionTree.SearchCNF
import Revres.Encoding.BinaryPointer
import Revres.SoD.Semantics
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Binary encoding of Sink-of-DAG

Every grid node owns one `ell`-bit successor block. Tagged semantic outputs are verified by local
adaptive trees of depth at most `2 * ell`, and their accepting leaves generate the canonical SoD
search CNF.
-/

namespace Revres

open Lemma53

namespace SoD

namespace Encoding

/-- Number of Boolean variables in the successor-only encoding. -/
def variableCount (ell : ℕ) : ℕ :=
  (BinaryPointer.order ell * BinaryPointer.order ell) * ell

/-- Flatten a grid node and a bit offset to one assignment coordinate. -/
def bitIndexEquiv (ell : ℕ) :
    (GridNode (BinaryPointer.order ell) × Fin ell) ≃ Fin (variableCount ell) :=
  (Equiv.prodCongr
      (finProdFinEquiv (m := BinaryPointer.order ell) (n := BinaryPointer.order ell))
      (Equiv.refl (Fin ell))).trans
    (finProdFinEquiv
      (m := BinaryPointer.order ell * BinaryPointer.order ell) (n := ell))

/-- Assignment coordinate of one successor bit. -/
def successorBit {ell : ℕ} (u : GridNode (BinaryPointer.order ell)) (b : Fin ell) :
    Fin (variableCount ell) :=
  bitIndexEquiv ell (u, b)

/-- The unique grid node whose successor record contains an encoded coordinate. -/
def nodeOfBit (ell : ℕ) (i : Fin (variableCount ell)) :
    GridNode (BinaryPointer.order ell) :=
  ((bitIndexEquiv ell).symm i).1

/-- All encoded successor coordinates belonging to one grid node. -/
def nodeBits (ell : ℕ) (u : GridNode (BinaryPointer.order ell)) :
    Finset (Fin (variableCount ell)) :=
  Finset.univ.image fun b => successorBit u b

@[simp]
theorem nodeOfBit_successorBit {ell : ℕ}
    (u : GridNode (BinaryPointer.order ell)) (b : Fin ell) :
    nodeOfBit ell (successorBit u b) = u := by
  simp [nodeOfBit, successorBit]

theorem mem_nodeBits_iff {ell : ℕ} {u : GridNode (BinaryPointer.order ell)}
    {i : Fin (variableCount ell)} :
    i ∈ nodeBits ell u ↔ nodeOfBit ell i = u := by
  constructor
  · intro hi
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hi
    exact nodeOfBit_successorBit u b
  · intro hi
    let index := (bitIndexEquiv ell).symm i
    have htuple : (u, index.2) = index := by
      apply Prod.ext
      · exact hi.symm
      · rfl
    have hcoord : successorBit u index.2 = i := by
      calc
        successorBit u index.2 = bitIndexEquiv ell index := by
          rw [successorBit, htuple]
        _ = i := (bitIndexEquiv ell).apply_symm_apply i
    exact Finset.mem_image.mpr ⟨index.2, Finset.mem_univ _, hcoord⟩

@[simp]
theorem card_nodeBits (ell : ℕ) (u : GridNode (BinaryPointer.order ell)) :
    (nodeBits ell u).card = ell := by
  rw [nodeBits, Finset.card_image_of_injective]
  · simp
  · intro b c hbc
    have hp : (u, b) = (u, c) := (bitIndexEquiv ell).injective hbc
    exact congrArg Prod.snd hp

theorem nodeBits_disjoint {ell : ℕ} {u v : GridNode (BinaryPointer.order ell)}
    (huv : u ≠ v) :
    Disjoint (nodeBits ell u) (nodeBits ell v) := by
  rw [Finset.disjoint_left]
  intro i hiu hiv
  exact huv ((mem_nodeBits_iff.mp hiu).symm.trans (mem_nodeBits_iff.mp hiv))

/-- Decode every successor block into the semantic SoD input. -/
noncomputable def decodeInput {ell : ℕ} (x : Fin (variableCount ell) → F2) :
    SoD.Input (BinaryPointer.order ell) where
  successor u := BinaryPointer.decode fun b => x (successorBit u b)

/-- Encode every semantic successor into its unique bit block. -/
noncomputable def encodeInput {ell : ℕ} (s : SoD.Input (BinaryPointer.order ell)) :
    Fin (variableCount ell) → F2 :=
  fun i =>
    let index := (bitIndexEquiv ell).symm i
    BinaryPointer.encode (s.successor index.1) index.2

@[simp]
theorem decodeInput_successor {ell : ℕ} (x : Fin (variableCount ell) → F2)
    (u : GridNode (BinaryPointer.order ell)) :
    (decodeInput x).successor u =
      BinaryPointer.decode (fun b => x (successorBit u b)) :=
  rfl

@[simp]
theorem encodeInput_successorBit {ell : ℕ} (s : SoD.Input (BinaryPointer.order ell))
    (u : GridNode (BinaryPointer.order ell)) (b : Fin ell) :
    encodeInput s (successorBit u b) = BinaryPointer.encode (s.successor u) b := by
  simp [encodeInput, successorBit]

@[simp]
theorem decodeInput_encodeInput {ell : ℕ} (s : SoD.Input (BinaryPointer.order ell)) :
    decodeInput (encodeInput s) = s := by
  ext u
  simp

@[simp]
theorem encodeInput_decodeInput {ell : ℕ} (x : Fin (variableCount ell) → F2) :
    encodeInput (decodeInput x) = x := by
  funext i
  let index := (bitIndexEquiv ell).symm i
  change BinaryPointer.encode
      (BinaryPointer.decode (fun b => x (successorBit index.1 b))) index.2 = x i
  rw [BinaryPointer.encode_decode]
  have hi : successorBit index.1 index.2 = i := by
    exact (bitIndexEquiv ell).apply_symm_apply i
  rw [hi]

/-- Read the successor pointer at one grid node. -/
noncomputable def readSuccessor {ell : ℕ} (u : GridNode (BinaryPointer.order ell)) :
    DecisionTree (variableCount ell) (Option (Fin (BinaryPointer.order ell))) :=
  BinaryPointer.read (successorBit u)

@[simp]
theorem eval_readSuccessor {ell : ℕ} (u : GridNode (BinaryPointer.order ell))
    (x : Fin (variableCount ell) → F2) :
    (readSuccessor u).eval x = (decodeInput x).successor u := by
  simp [readSuccessor]

@[simp]
theorem depth_readSuccessor {ell : ℕ} (u : GridNode (BinaryPointer.order ell)) :
    (readSuccessor u).depth = ell := by
  simp [readSuccessor]

/-- Local verifier for one tagged SoD output. -/
noncomputable def verifier {ell : ℕ} (hell : 0 < ell) :
    SoD.Output (BinaryPointer.order ell) →
      DecisionTree (variableCount ell) Bool
  | .inactiveSource =>
      (readSuccessor (GridNode.distinguished (BinaryPointer.order_pos hell))).map
        fun pointer => decide (pointer = none)
  | .activeLast u =>
      if _hlast : u.IsLastRow then
        (readSuccessor u).map fun pointer => decide (pointer ≠ none)
      else
        .leaf false
  | .properSink u =>
      if hu : u.IsInternal then
        (readSuccessor u).bind fun pointer =>
          match pointer with
          | none => .leaf false
          | some column =>
              (readSuccessor (u.next hu column)).map
                fun target => decide (target = none)
      else
        .leaf false

private theorem properSinkWitness_iff_of_successor_eq_some
    {ell : ℕ} (s : SoD.Input (BinaryPointer.order ell))
    {u : GridNode (BinaryPointer.order ell)} (hu : u.IsInternal)
    {column : Fin (BinaryPointer.order ell)} (hs : s.successor u = some column) :
    s.ProperSinkWitness u ↔ s.successor (u.next hu column) = none := by
  let v := u.next hu column
  have huv : s.PointsTo u v := ⟨u.nextRow_next hu column, hs⟩
  constructor
  · rintro ⟨w, huw, hinactive⟩
    have hwv : w = v := s.pointsTo_target_unique huw huv
    subst w
    simpa [SoD.Input.Active] using hinactive
  · intro hv
    refine ⟨v, huv, ?_⟩
    simpa [SoD.Input.Active, v] using hv

theorem verifier_correct {ell : ℕ} (hell : 0 < ell)
    (o : SoD.Output (BinaryPointer.order ell))
    (x : Fin (variableCount ell) → F2) :
    (verifier hell o).eval x = true ↔
      SoD.Valid (BinaryPointer.order_pos hell) (decodeInput x) o := by
  cases o with
  | inactiveSource =>
      simp [verifier, SoD.Valid, SoD.Input.Active]
  | activeLast u =>
      by_cases hlast : u.IsLastRow
      · simp [verifier, hlast, SoD.Valid, SoD.Input.Active]
      · simp [verifier, hlast, SoD.Valid]
  | properSink u =>
      by_cases hu : u.IsInternal
      · cases hs : (decodeInput x).successor u with
        | none =>
            have hnot : ¬(decodeInput x).ProperSinkWitness u := by
              rintro ⟨v, hpoints, _hinactive⟩
              rw [SoD.Input.PointsTo, hs] at hpoints
              simp at hpoints
            have hsbits :
                BinaryPointer.decode (fun b => x (successorBit u b)) = none := by
              simpa using hs
            simp [verifier, hu, hsbits, SoD.Valid, hnot]
        | some column =>
            have hwitness := properSinkWitness_iff_of_successor_eq_some
              (decodeInput x) hu hs
            have hsbits :
                BinaryPointer.decode (fun b => x (successorBit u b)) = some column := by
              simpa using hs
            simp [verifier, hu, hsbits, SoD.Valid, hwitness]
      · have hnot : ¬(decodeInput x).ProperSinkWitness u := by
          rintro ⟨v, hpoints, _hinactive⟩
          exact hu (GridNode.nextRow_internal hpoints.1)
        simp [verifier, hu, SoD.Valid, hnot]

theorem verifier_depth_le {ell : ℕ} (hell : 0 < ell)
    (o : SoD.Output (BinaryPointer.order ell)) :
    (verifier hell o).depth ≤ 2 * ell := by
  cases o with
  | inactiveSource => simp [verifier, two_mul]
  | activeLast u =>
      by_cases hlast : u.IsLastRow <;> simp [verifier, hlast, two_mul]
  | properSink u =>
      by_cases hu : u.IsInternal
      · let next := fun pointer : Option (Fin (BinaryPointer.order ell)) =>
          match pointer with
          | none => DecisionTree.leaf false
          | some column =>
              (readSuccessor (u.next hu column)).map
                fun target => decide (target = none)
        have hnext : ∀ pointer, (next pointer).depth ≤ ell := by
          intro pointer
          cases pointer <;> simp [next]
        have hbind := DecisionTree.depth_bind_le (readSuccessor u) next hnext
        simpa [verifier, hu, next, two_mul] using hbind
      · simp [verifier, hu]

/-- The encoded finite total SoD search problem. -/
noncomputable def searchProblem (ell : ℕ) (hell : 0 < ell) :
    SearchProblem (variableCount ell) where
  Output := SoD.Output (BinaryPointer.order ell)
  instOutputFintype := inferInstance
  valid x o := SoD.Valid (BinaryPointer.order_pos hell) (decodeInput x) o
  total x := SoD.total (BinaryPointer.order_pos hell) (decodeInput x)
  verifier := verifier hell
  verifier_correct := fun x o => verifier_correct hell o x

theorem searchProblem_verifierDepth_le (ell : ℕ) (hell : 0 < ell) :
    (searchProblem ell hell).verifierDepth ≤ 2 * ell := by
  classical
  rw [SearchProblem.verifierDepth]
  exact Finset.sup_le fun o _ho => verifier_depth_le hell o

/-- Canonical binary SoD search CNF. -/
noncomputable def searchCNF (ell : ℕ) (hell : 0 < ell) : CNF (variableCount ell) :=
  (searchProblem ell hell).toCNF

/-- Fixed semantic output label of a canonical SoD clause. -/
noncomputable def clauseOutput {ell : ℕ} {hell : 0 < ell}
    (C : ↑(searchCNF ell hell)) : SoD.Output (BinaryPointer.order ell) :=
  (searchProblem ell hell).clauseOutput C

theorem clauseOutput_valid {ell : ℕ} {hell : 0 < ell}
    (C : ↑(searchCNF ell hell)) {x : Fin (variableCount ell) → F2}
    (hC : C.1.Falsified x) :
    SoD.Valid (BinaryPointer.order_pos hell) (decodeInput x) (clauseOutput C) :=
  (searchProblem ell hell).clauseOutput_valid C hC

theorem searchCNF_unsat (ell : ℕ) (hell : 0 < ell) :
    (searchCNF ell hell).Unsat :=
  (searchProblem ell hell).toCNF_unsat

theorem searchCNF_width_le (ell : ℕ) (hell : 0 < ell) :
    (searchCNF ell hell).width ≤ 2 * ell :=
  (searchProblem ell hell).toCNF_width_le_verifierDepth.trans
    (searchProblem_verifierDepth_le ell hell)

/-- Every canonical SoD clause contains at least one encoded input variable. -/
theorem one_le_width_searchCNF_clause
    {ell : ℕ} {hell : 0 < ell} (C : ↑(searchCNF ell hell)) :
    1 ≤ C.1.width := by
  by_contra hwidth
  have hzero : C.1.width = 0 := Nat.eq_zero_of_not_pos hwidth
  have hsupport : C.1.support = ∅ := by
    exact Finset.card_eq_zero.mp (by simpa [Clause.width] using hzero)
  have hfalsified : ∀ x : Fin (variableCount ell) → F2, C.1.Falsified x := by
    intro x i b hib
    have hi : i ∈ C.1.support := by simp [hib]
    rw [hsupport] at hi
    simp at hi
  cases ho : clauseOutput C with
  | inactiveSource =>
      let zeroColumn : Fin (BinaryPointer.order ell) :=
        ⟨0, BinaryPointer.order_pos hell⟩
      let s : SoD.Input (BinaryPointer.order ell) :=
        ⟨fun _ => some zeroColumn⟩
      have hvalid := clauseOutput_valid C
        (x := encodeInput s) (hfalsified (encodeInput s))
      rw [ho] at hvalid
      exact hvalid (by simp [SoD.Input.Active, s])
  | activeLast u =>
      let s : SoD.Input (BinaryPointer.order ell) := ⟨fun _ => none⟩
      have hvalid := clauseOutput_valid C
        (x := encodeInput s) (hfalsified (encodeInput s))
      rw [ho] at hvalid
      exact hvalid.2 (by simp [s])
  | properSink u =>
      let s : SoD.Input (BinaryPointer.order ell) := ⟨fun _ => none⟩
      have hvalid := clauseOutput_valid C
        (x := encodeInput s) (hfalsified (encodeInput s))
      rw [ho] at hvalid
      obtain ⟨v, hpoints, _hinactive⟩ := hvalid
      simp [SoD.Input.PointsTo, s] at hpoints

theorem inactiveSource_clauses_falsified_iff
    {ell : ℕ} (hell : 0 < ell) (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses (.inactiveSource),
      C.Falsified x) ↔
      ¬(decodeInput x).Active
        (GridNode.distinguished (BinaryPointer.order_pos hell)) := by
  simpa [searchProblem, SoD.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.inactiveSource) x)

theorem activeLast_clauses_falsified_iff
    {ell : ℕ} (hell : 0 < ell) (u : GridNode (BinaryPointer.order ell))
    (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses (.activeLast u),
      C.Falsified x) ↔
      u.IsLastRow ∧ (decodeInput x).Active u := by
  simpa [searchProblem, SoD.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.activeLast u) x)

theorem properSink_clauses_falsified_iff
    {ell : ℕ} (hell : 0 < ell) (u : GridNode (BinaryPointer.order ell))
    (x : Fin (variableCount ell) → F2) :
    (∃ C ∈ (searchProblem ell hell).outputClauses (.properSink u),
      C.Falsified x) ↔ (decodeInput x).ProperSinkWitness u := by
  simpa [searchProblem, SoD.Valid] using
    ((searchProblem ell hell).exists_falsified_mem_outputClauses_iff
      (.properSink u) x)

end Encoding

end SoD

end Revres
