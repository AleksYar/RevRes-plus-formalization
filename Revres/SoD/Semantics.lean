import Revres.Grid.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Sink-of-DAG semantics

An SoD input stores one optional successor column at every grid node. Internal nonnull pointers
advance to the next row, while a nonnull pointer on the last row represents an edge leaving the
grid. Fan-out is at most one and fan-in is unrestricted.
-/

namespace Revres

namespace SoD

/-- Semantic successor data on an `n`-by-`n` grid. -/
@[ext]
structure Input (n : ℕ) where
  successor : GridNode n → Option (Fin n)
deriving DecidableEq

namespace Input

variable {n : ℕ}

/-- An internal successor pointer between consecutive rows. -/
def PointsTo (x : Input n) (u v : GridNode n) : Prop :=
  u.NextRow v ∧ x.successor u = some v.column

instance pointsToDecidable (x : Input n) (u v : GridNode n) :
    Decidable (x.PointsTo u v) := by
  unfold PointsTo
  infer_instance

/-- The target of an internal nonnull successor, when it exists. -/
def nextNode (x : Input n) (u : GridNode n) : Option (GridNode n) :=
  if hu : u.IsInternal then
    match x.successor u with
    | none => none
    | some c => some (u.next hu c)
  else
    none

private theorem next_eq_of_pointsTo_of_successor
    {x : Input n} {u v : GridNode n} (hu : u.IsInternal) {c : Fin n}
    (hs : x.successor u = some c) (hpoints : x.PointsTo u v) :
    u.next hu c = v := by
  apply Prod.ext
  · apply Fin.ext
    change u.row.val + 1 = v.row.val
    exact hpoints.1.symm
  · exact Option.some.inj (hs.symm.trans hpoints.2)

theorem nextNode_eq_some_iff
    (x : Input n) (u v : GridNode n) :
    x.nextNode u = some v ↔ x.PointsTo u v := by
  by_cases hu : u.IsInternal
  · cases hs : x.successor u with
    | none => simp [nextNode, hu, hs, PointsTo]
    | some c =>
        constructor
        · intro hnext
          have huv : u.next hu c = v := by
            simpa [nextNode, hu, hs] using hnext
          subst v
          exact ⟨u.nextRow_next hu c, hs⟩
        · intro hpoints
          have huv : u.next hu c = v :=
            next_eq_of_pointsTo_of_successor hu hs hpoints
          subst v
          simp [nextNode, hu, hs]
  · constructor
    · intro hnext
      simp [nextNode, hu] at hnext
    · intro hpoints
      exact (hu (GridNode.nextRow_internal hpoints.1)).elim

/-- Every source has at most one internal pointer target. -/
theorem pointsTo_target_unique
    {x : Input n} {u v w : GridNode n}
    (huv : x.PointsTo u v) (huw : x.PointsTo u w) :
    v = w := by
  apply Prod.ext
  · exact GridNode.nextRow_row_unique huv.1 huw.1
  · exact Option.some.inj (huv.2.symm.trans huw.2)

/-- A node is active exactly when its successor datum is nonnull. -/
def Active (x : Input n) (u : GridNode n) : Prop :=
  x.successor u ≠ none

instance activeDecidable (x : Input n) (u : GridNode n) :
    Decidable (x.Active u) := by
  unfold Active
  infer_instance

theorem active_internal_iff_exists_pointsTo
    (x : Input n) {u : GridNode n} (hu : u.IsInternal) :
    x.Active u ↔ ∃ v, x.PointsTo u v := by
  constructor
  · intro hactive
    cases hs : x.successor u with
    | none => exact (hactive hs).elim
    | some c => exact ⟨u.next hu c, u.nextRow_next hu c, hs⟩
  · rintro ⟨v, hpoints⟩ hnone
    exact Option.some_ne_none _ (hpoints.2.symm.trans hnone)

theorem active_lastRow_iff
    (x : Input n) {u : GridNode n} (_hu : u.IsLastRow) :
    x.Active u ↔ x.successor u ≠ none :=
  Iff.rfl

/-- A geometric proper sink is an inactive target of an internal pointer. -/
def ProperSink (x : Input n) (v : GridNode n) : Prop :=
  ¬x.Active v ∧ ∃ u, x.PointsTo u v

instance properSinkDecidable (x : Input n) (v : GridNode n) :
    Decidable (x.ProperSink v) := by
  unfold ProperSink
  infer_instance

/-- The predecessor-labelled form of a proper-sink witness used by the canonical search problem. -/
def ProperSinkWitness (x : Input n) (u : GridNode n) : Prop :=
  ∃ v, x.PointsTo u v ∧ ¬x.Active v

instance properSinkWitnessDecidable (x : Input n) (u : GridNode n) :
    Decidable (x.ProperSinkWitness u) := by
  unfold ProperSinkWitness
  infer_instance

/-- A predecessor-labelled witness determines one geometric proper sink. -/
theorem properSink_of_witness
    (x : Input n) {u : GridNode n} (h : x.ProperSinkWitness u) :
    ∃! v, x.PointsTo u v ∧ x.ProperSink v := by
  obtain ⟨v, hpoints, hinactive⟩ := h
  refine ⟨v, ⟨hpoints, hinactive, ⟨u, hpoints⟩⟩, ?_⟩
  intro w hw
  exact x.pointsTo_target_unique hw.1 hpoints

/-- Geometric sinks are exactly targets of predecessor-labelled sink witnesses. -/
theorem properSink_iff_exists_witness
    (x : Input n) {v : GridNode n} :
    x.ProperSink v ↔ ∃ u, x.PointsTo u v ∧ x.ProperSinkWitness u := by
  constructor
  · rintro ⟨hinactive, u, hpoints⟩
    exact ⟨u, hpoints, v, hpoints, hinactive⟩
  · rintro ⟨u, huv, w, huw, hinactive⟩
    have hwv : w = v := x.pointsTo_target_unique huw huv
    exact ⟨hwv ▸ hinactive, ⟨u, huv⟩⟩

/-- One walk step either remains active or gives a predecessor-labelled proper-sink witness. -/
theorem active_internal_step
    (x : Input n) {u : GridNode n}
    (hactive : x.Active u) (hu : u.IsInternal) :
    ∃ v, x.PointsTo u v ∧ (x.Active v ∨ x.ProperSinkWitness u) := by
  obtain ⟨v, hpoints⟩ := (x.active_internal_iff_exists_pointsTo hu).mp hactive
  refine ⟨v, hpoints, ?_⟩
  by_cases hv : x.Active v
  · exact Or.inl hv
  · exact Or.inr ⟨v, hpoints, hv⟩

end Input

/-- The three kinds of local SoD witnesses.
A proper sink is labelled by its predecessor. -/
inductive Output (n : ℕ)
  | inactiveSource
  | activeLast (u : GridNode n)
  | properSink (u : GridNode n)
deriving DecidableEq, Fintype

/-- Semantic validity of a tagged SoD output. -/
def Valid {n : ℕ} (hn : 0 < n) (x : Input n) : Output n → Prop
  | .inactiveSource => ¬x.Active (GridNode.distinguished hn)
  | .activeLast u => u.IsLastRow ∧ x.Active u
  | .properSink u => x.ProperSinkWitness u

instance validDecidable {n : ℕ} (hn : 0 < n) (x : Input n) (o : Output n) :
    Decidable (Valid hn x o) := by
  cases o <;> simp only [Valid] <;> infer_instance

/-- A valid canonical sink output recovers its unique geometric sink target. -/
theorem valid_properSink_geometric
    {n : ℕ} {hn : 0 < n} {x : Input n} {u : GridNode n}
    (h : Valid hn x (.properSink u)) :
    ∃! v, x.PointsTo u v ∧ x.ProperSink v :=
  x.properSink_of_witness h

private theorem exists_activeLast_or_properSinkWitness_from_active
    {n : ℕ} (x : Input n) (u : GridNode n) (hactive : x.Active u) :
    (∃ v, v.IsLastRow ∧ x.Active v) ∨ ∃ w, x.ProperSinkWitness w := by
  rcases u.internal_or_last with hu | hu
  · obtain ⟨v, hpoints, hv | hsink⟩ := x.active_internal_step hactive hu
    · exact exists_activeLast_or_properSinkWitness_from_active x v hv
    · exact Or.inr ⟨u, hsink⟩
  · exact Or.inl ⟨u, hu, hactive⟩
termination_by n - u.row.val
decreasing_by
  have huv : u.row.val < v.row.val := by
    rw [hpoints.1]
    exact Nat.lt_succ_self _
  exact Nat.sub_lt_sub_left u.row.isLt huv

/-- Every positive-order semantic SoD input has a valid local output. -/
theorem total {n : ℕ} (hn : 0 < n) (x : Input n) :
    ∃ o : Output n, Valid hn x o := by
  let source := GridNode.distinguished hn
  by_cases hsource : x.Active source
  · rcases exists_activeLast_or_properSinkWitness_from_active x source hsource with
      ⟨u, hlast, hactive⟩ | ⟨u, hsink⟩
    · exact ⟨Output.activeLast u, hlast, hactive⟩
    · exact ⟨Output.properSink u, hsink⟩
  · exact ⟨Output.inactiveSource, hsource⟩

end SoD

end Revres
