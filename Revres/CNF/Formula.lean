import Revres.CNF.Clause

/-!
# Ordinary CNF formulas
-/

namespace Revres

open Lemma53

variable {N : ℕ}

/-- A CNF is a finite set of canonical ordinary clauses. -/
abbrev CNF (N : ℕ) := Finset (Clause N)

namespace CNF

/-- Every assignment falsifies at least one clause of an unsatisfiable CNF. -/
def Unsat (F : CNF N) : Prop :=
  ∀ x : Fin N → F2, ∃ C ∈ F, C.Falsified x

/-- The maximum width of a clause in a CNF. -/
def width (F : CNF N) : ℕ :=
  F.sup Clause.width

theorem clause_width_le_width {F : CNF N} {C : Clause N} (hC : C ∈ F) :
    C.width ≤ F.width :=
  Finset.le_sup hC

@[simp]
theorem width_empty : width (∅ : CNF N) = 0 :=
  rfl

end CNF

end Revres
