import Revres.Grid.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Sink-of-Potential-Line semantics

The input stores semantic successor and predecessor names. An internal edge is active precisely
when the two pointer names agree. The resulting layered graph has active in-degree and out-degree
at most one.
-/

namespace Revres

namespace SoPL

/-- Semantic successor and predecessor pointer data on an `n`-by-`n` grid. -/
@[ext]
structure Input (n : ℕ) where
  successor : GridNode n → Option (Fin n)
  predecessor : GridNode n → Option (Fin n)
deriving DecidableEq

namespace Input

variable {n : ℕ}

/-- A mutually certified edge between consecutive rows. -/
def ActiveEdge (x : Input n) (u v : GridNode n) : Prop :=
  u.NextRow v ∧
    x.successor u = some v.column ∧
    x.predecessor v = some u.column

instance activeEdgeDecidable (x : Input n) (u v : GridNode n) :
    Decidable (x.ActiveEdge u v) := by
  unfold ActiveEdge
  infer_instance

/-- The unique active successor computed from the two pointer names, when it exists. -/
def nextNode (x : Input n) (u : GridNode n) : Option (GridNode n) :=
  if hu : u.IsInternal then
    match x.successor u with
    | none => none
    | some c =>
        let v := u.next hu c
        if x.predecessor v = some u.column then some v else none
  else
    none

private theorem next_eq_of_activeEdge_of_successor
    {x : Input n} {u v : GridNode n} (hu : u.IsInternal) {c : Fin n}
    (hs : x.successor u = some c) (hedge : x.ActiveEdge u v) :
    u.next hu c = v := by
  apply Prod.ext
  · apply Fin.ext
    change u.row.val + 1 = v.row.val
    exact hedge.1.symm
  · exact Option.some.inj (hs.symm.trans hedge.2.1)

theorem nextNode_eq_some_iff
    (x : Input n) (u v : GridNode n) :
    x.nextNode u = some v ↔ x.ActiveEdge u v := by
  by_cases hu : u.IsInternal
  · cases hs : x.successor u with
    | none => simp [nextNode, hu, hs, ActiveEdge]
    | some c =>
        let w := u.next hu c
        by_cases hp : x.predecessor w = some u.column
        · constructor
          · intro hnext
            have hwv : w = v := by
              simpa [nextNode, hu, hs, w, hp] using hnext
            subst v
            refine ⟨u.nextRow_next hu c, ?_, hp⟩
            change x.successor u = some c
            exact hs
          · intro hedge
            have hwv : w = v :=
              next_eq_of_activeEdge_of_successor hu hs hedge
            subst v
            simp [nextNode, hu, hs, w, hp]
        · constructor
          · intro hnext
            have hnext' : x.predecessor w = some u.column ∧ w = v := by
              simpa [nextNode, hu, hs, w] using hnext
            exact (hp hnext'.1).elim
          · intro hedge
            have hwv : w = v :=
              next_eq_of_activeEdge_of_successor hu hs hedge
            subst v
            exact (hp hedge.2.2).elim
  · constructor
    · intro hnext
      simp [nextNode, hu] at hnext
    · intro hedge
      exact (hu (GridNode.nextRow_internal hedge.1)).elim

theorem activeEdge_target_unique
    {x : Input n} {u v w : GridNode n}
    (huv : x.ActiveEdge u v) (huw : x.ActiveEdge u w) :
    v = w := by
  apply Prod.ext
  · exact GridNode.nextRow_row_unique huv.1 huw.1
  · exact Option.some.inj (huv.2.1.symm.trans huw.2.1)

theorem activeEdge_source_unique
    {x : Input n} {u v w : GridNode n}
    (huv : x.ActiveEdge u v) (hwv : x.ActiveEdge w v) :
    u = w := by
  apply Prod.ext
  · exact GridNode.nextRow_source_row_unique huv.1 hwv.1
  · exact Option.some.inj (huv.2.2.symm.trans hwv.2.2)

/-- Internal activity is an outgoing certified edge; last-row activity is a nonnull successor. -/
def Active (x : Input n) (u : GridNode n) : Prop :=
  (∃ v, x.ActiveEdge u v) ∨
    (u.IsLastRow ∧ x.successor u ≠ none)

instance activeDecidable (x : Input n) (u : GridNode n) :
    Decidable (x.Active u) := by
  unfold Active
  infer_instance

/-- An inactive target of an incoming active edge. -/
def ProperSink (x : Input n) (v : GridNode n) : Prop :=
  ¬x.Active v ∧ ∃ u, x.ActiveEdge u v

instance properSinkDecidable (x : Input n) (v : GridNode n) :
    Decidable (x.ProperSink v) := by
  unfold ProperSink
  infer_instance

theorem active_internal_iff
    (x : Input n) {u : GridNode n} (hu : u.IsInternal) :
    x.Active u ↔ ∃ v, x.ActiveEdge u v := by
  constructor
  · rintro (hedge | ⟨hlast, _hsucc⟩)
    · exact hedge
    · exact (GridNode.not_last_of_internal hu hlast).elim
  · exact Or.inl

theorem active_lastRow_iff
    (x : Input n) {u : GridNode n} (hu : u.IsLastRow) :
    x.Active u ↔ x.successor u ≠ none := by
  constructor
  · rintro (⟨v, hedge⟩ | ⟨_hlast, hsucc⟩)
    · exact (GridNode.not_internal_of_last hu
        (GridNode.nextRow_internal hedge.1)).elim
    · exact hsucc
  · exact fun hsucc ↦ Or.inr ⟨hu, hsucc⟩

/-- One walk step either remains active or reaches a proper sink. -/
theorem active_internal_step
    (x : Input n) {u : GridNode n}
    (hactive : x.Active u) (hu : u.IsInternal) :
    ∃ v, x.ActiveEdge u v ∧ (x.Active v ∨ x.ProperSink v) := by
  obtain ⟨v, hedge⟩ := (x.active_internal_iff hu).mp hactive
  refine ⟨v, hedge, ?_⟩
  by_cases hv : x.Active v
  · exact Or.inl hv
  · exact Or.inr ⟨hv, ⟨u, hedge⟩⟩

end Input

/-- The three distinct kinds of local SoPL witnesses. -/
inductive Output (n : ℕ)
  | inactiveSource
  | activeLast (u : GridNode n)
  | properSink (v : GridNode n)
deriving DecidableEq, Fintype

/-- Semantic validity of a tagged SoPL output. -/
def Valid {n : ℕ} (hn : 0 < n) (x : Input n) : Output n → Prop
  | .inactiveSource => ¬x.Active (GridNode.distinguished hn)
  | .activeLast u => u.IsLastRow ∧ x.Active u
  | .properSink v => x.ProperSink v

instance validDecidable {n : ℕ} (hn : 0 < n) (x : Input n) (o : Output n) :
    Decidable (Valid hn x o) := by
  cases o <;> simp only [Valid] <;> infer_instance

private theorem exists_activeLast_or_properSink_from_active
    {n : ℕ} (x : Input n) (u : GridNode n) (hactive : x.Active u) :
    (∃ v, v.IsLastRow ∧ x.Active v) ∨ ∃ v, x.ProperSink v := by
  rcases u.internal_or_last with hu | hu
  · obtain ⟨v, hedge, hv | hsink⟩ := x.active_internal_step hactive hu
    · exact exists_activeLast_or_properSink_from_active x v hv
    · exact Or.inr ⟨v, hsink⟩
  · exact Or.inl ⟨u, hu, hactive⟩
termination_by n - u.row.val
decreasing_by
  have huv : u.row.val < v.row.val := by
    rw [hedge.1]
    exact Nat.lt_succ_self _
  exact Nat.sub_lt_sub_left u.row.isLt huv

theorem total {n : ℕ} (hn : 0 < n) (x : Input n) :
    ∃ o : Output n, Valid hn x o := by
  let source := GridNode.distinguished hn
  by_cases hsource : x.Active source
  · rcases exists_activeLast_or_properSink_from_active x source hsource with
      ⟨u, hlast, hactive⟩ | ⟨v, hsink⟩
    · exact ⟨Output.activeLast u, hlast, hactive⟩
    · exact ⟨Output.properSink v, hsink⟩
  · exact ⟨Output.inactiveSource, hsource⟩

end SoPL

end Revres
