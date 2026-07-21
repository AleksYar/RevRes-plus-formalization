import Lemma53.Gadget
import Mathlib.Data.Finset.Card

/-!
# Ordinary clauses

An ordinary clause is represented by its unique falsifying partial assignment. This avoids
literal-order and duplicate-literal quotients.
-/

namespace Revres

open Lemma53

variable {N : ℕ}

/-- An ordinary clause on `N` variables, represented by its falsifying partial assignment. -/
abbrev Clause (N : ℕ) := Fin N → Option F2

namespace Clause

/-- An assignment falsifies a clause when it agrees with every specified falsifying bit. -/
def Falsified (C : Clause N) (x : Fin N → F2) : Prop :=
  ∀ i b, C i = some b → x i = b

/-- The variables occurring in a clause. -/
def support (C : Clause N) : Finset (Fin N) :=
  Finset.univ.filter fun i => C i ≠ none

@[simp] theorem mem_support {C : Clause N} {i : Fin N} :
    i ∈ C.support ↔ C i ≠ none := by
  simp [support]

@[simp] theorem not_mem_support {C : Clause N} {i : Fin N} :
    i ∉ C.support ↔ C i = none := by
  simp

/-- The number of variables occurring in a clause. -/
def width (C : Clause N) : ℕ :=
  C.support.card

/-- A clause cannot contain more variables than the ambient assignment. -/
theorem width_le (C : Clause N) : C.width ≤ N := by
  rw [width]
  simpa using Finset.card_le_card (Finset.subset_univ C.support)

/-- The empty ordinary clause. -/
def empty (N : ℕ) : Clause N :=
  fun _ => none

@[simp] theorem empty_falsified (x : Fin N → F2) :
    (empty N).Falsified x := by
  simp [Falsified, empty]

@[simp] theorem support_empty : (empty N).support = ∅ := by
  ext i
  simp [empty]

@[simp] theorem width_empty : (empty N).width = 0 := by
  simp [width]

end Clause

end Revres
