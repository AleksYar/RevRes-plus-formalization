import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Finite square grids

Grid nodes retain separate row and column coordinates. Rows increase by one along every semantic
edge used by the layered search problems.
-/

namespace Revres

/-- A node in an `n`-by-`n` grid. -/
abbrev GridNode (n : ℕ) := Fin n × Fin n

namespace GridNode

variable {n : ℕ}

/-- The row coordinate of a grid node. -/
@[simp]
def row (u : GridNode n) : Fin n :=
  u.1

/-- The column coordinate of a grid node. -/
@[simp]
def column (u : GridNode n) : Fin n :=
  u.2

/-- A node is in the first row. -/
def IsFirstRow (u : GridNode n) : Prop :=
  u.row.val = 0

/-- A node is in the last row. -/
def IsLastRow (u : GridNode n) : Prop :=
  u.row.val + 1 = n

/-- A node has a row below it. -/
def IsInternal (u : GridNode n) : Prop :=
  u.row.val + 1 < n

/-- The second node is exactly one row below the first. -/
def NextRow (u v : GridNode n) : Prop :=
  v.row.val = u.row.val + 1

instance isFirstRowDecidable (u : GridNode n) : Decidable u.IsFirstRow :=
  inferInstanceAs (Decidable (u.row.val = 0))

instance isLastRowDecidable (u : GridNode n) : Decidable u.IsLastRow :=
  inferInstanceAs (Decidable (u.row.val + 1 = n))

instance isInternalDecidable (u : GridNode n) : Decidable u.IsInternal :=
  inferInstanceAs (Decidable (u.row.val + 1 < n))

instance nextRowDecidable (u v : GridNode n) : Decidable (u.NextRow v) :=
  inferInstanceAs (Decidable (v.row.val = u.row.val + 1))

/-- The distinguished top-left node. -/
def distinguished (hn : 0 < n) : GridNode n :=
  (⟨0, hn⟩, ⟨0, hn⟩)

/-- The node one row below `u` in column `c`. -/
def next (u : GridNode n) (hu : u.IsInternal) (c : Fin n) : GridNode n :=
  (⟨u.row.val + 1, hu⟩, c)

@[simp]
theorem row_next (u : GridNode n) (hu : u.IsInternal) (c : Fin n) :
    (u.next hu c).row.val = u.row.val + 1 :=
  rfl

@[simp]
theorem column_next (u : GridNode n) (hu : u.IsInternal) (c : Fin n) :
    (u.next hu c).column = c :=
  rfl

theorem nextRow_next (u : GridNode n) (hu : u.IsInternal) (c : Fin n) :
    u.NextRow (u.next hu c) :=
  rfl

theorem internal_or_last (u : GridNode n) :
    u.IsInternal ∨ u.IsLastRow := by
  unfold IsInternal IsLastRow
  exact lt_or_eq_of_le (Nat.succ_le_iff.mpr u.row.isLt)

theorem not_last_of_internal {u : GridNode n} (hu : u.IsInternal) :
    ¬u.IsLastRow := by
  unfold IsInternal IsLastRow at *
  exact Nat.ne_of_lt hu

theorem not_internal_of_last {u : GridNode n} (hu : u.IsLastRow) :
    ¬u.IsInternal := by
  unfold IsInternal IsLastRow at *
  intro hi
  exact (Nat.ne_of_lt hi) hu

theorem nextRow_internal {u v : GridNode n} (h : u.NextRow v) :
    u.IsInternal := by
  unfold NextRow IsInternal at *
  exact h ▸ v.row.isLt

theorem nextRow_ne {u v : GridNode n} (h : u.NextRow v) :
    u ≠ v := by
  intro huv
  subst v
  unfold NextRow at h
  exact (Nat.ne_of_lt (Nat.lt_succ_self u.row.val)) h

theorem nextRow_row_unique {u v w : GridNode n}
    (huv : u.NextRow v) (huw : u.NextRow w) :
    v.row = w.row := by
  apply Fin.ext
  unfold NextRow at huv huw
  exact huv.trans huw.symm

theorem nextRow_source_row_unique {u v w : GridNode n}
    (huw : u.NextRow w) (hvw : v.NextRow w) :
    u.row = v.row := by
  apply Fin.ext
  unfold NextRow at huw hvw
  exact Nat.add_right_cancel (huw.symm.trans hvw)

theorem eq_next_of_nextRow {u v : GridNode n} (h : u.NextRow v) :
    u.next (nextRow_internal h) v.column = v := by
  apply Prod.ext
  · apply Fin.ext
    change u.row.val + 1 = v.row.val
    exact h.symm
  · rfl

@[simp]
theorem distinguished_isFirstRow (hn : 0 < n) :
    (distinguished hn).IsFirstRow :=
  rfl

@[simp]
theorem row_distinguished (hn : 0 < n) :
    (distinguished hn).row = ⟨0, hn⟩ :=
  rfl

@[simp]
theorem column_distinguished (hn : 0 < n) :
    (distinguished hn).column = ⟨0, hn⟩ :=
  rfl

end GridNode

end Revres
