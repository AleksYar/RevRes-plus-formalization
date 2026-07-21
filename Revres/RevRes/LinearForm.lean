import Lemma53.Gadget
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# Linear forms and parity equations

This file defines parity equations over an arbitrary `F2`-vector space and their pointwise
semantics.
-/

namespace Revres

open Lemma53
open scoped CharTwo

variable {X : Type*} [AddCommGroup X] [Module F2 X]

/-- A parity equation `lhs = rhs` over an `F2`-vector space. -/
structure ParityEquation (X : Type*) [AddCommGroup X] [Module F2 X] where
  lhs : X →ₗ[F2] F2
  rhs : F2

namespace ParityEquation

/-- The equation holds at `x`. -/
def Satisfied (e : ParityEquation X) (x : X) : Prop :=
  e.lhs x = e.rhs

/-- Over `F2`, falsifying `lhs = rhs` means attaining the other field element. -/
def Falsified (e : ParityEquation X) (x : X) : Prop :=
  e.lhs x = e.rhs + 1

instance (e : ParityEquation X) (x : X) : Decidable (e.Falsified x) :=
  inferInstanceAs (Decidable (e.lhs x = e.rhs + 1))

/-- The equation with right-hand side zero for a given linear form. -/
def eqZero (lhs : X →ₗ[F2] F2) : ParityEquation X :=
  ⟨lhs, 0⟩

/-- The equation with right-hand side one for a given linear form. -/
def eqOne (lhs : X →ₗ[F2] F2) : ParityEquation X :=
  ⟨lhs, 1⟩

end ParityEquation

/-- Two `F2` elements differ exactly when the first is the additive complement of the second. -/
lemma F2_ne_iff_eq_add_one (a b : F2) :
    a ≠ b ↔ a = b + 1 := by
  rcases F2_eq_zero_or_one a with rfl | rfl <;>
    rcases F2_eq_zero_or_one b with rfl | rfl <;> simp

namespace ParityEquation

@[simp] theorem falsified_iff_not_satisfied (e : ParityEquation X) (x : X) :
    e.Falsified x ↔ ¬ e.Satisfied x := by
  exact (F2_ne_iff_eq_add_one (e.lhs x) e.rhs).symm

end ParityEquation

end Revres
