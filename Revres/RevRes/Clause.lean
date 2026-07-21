import Revres.RevRes.LinearForm
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Parity clauses

Parity clauses are lists of equations, interpreted as disjunctions. Their common falsifying set
is also exposed as an affine subspace.
-/

namespace Revres

open Lemma53

variable {X : Type*} [AddCommGroup X] [Module F2 X]

/-- A parity clause is a disjunction of parity equations. -/
abbrev ParityClause (X : Type*) [AddCommGroup X] [Module F2 X] := List (ParityEquation X)

namespace ParityClause

/-- A clause is falsified when all of its equations are falsified. -/
def Falsified : ParityClause X → X → Prop
  | [], _ => True
  | e :: C, x => e.Falsified x ∧ Falsified C x

instance (C : ParityClause X) (x : X) : Decidable (C.Falsified x) := by
  induction C with
  | nil => exact isTrue trivial
  | cons e C ih =>
      change Decidable (e.Falsified x ∧ Falsified C x)
      letI := ih
      infer_instance

@[simp] theorem empty_falsified (x : X) :
    Falsified ([] : ParityClause X) x := by
  simp [Falsified]

/-- Adjoin one equation to a parity clause. -/
def withEquation (C : ParityClause X) (e : ParityEquation X) : ParityClause X :=
  e :: C

@[simp] theorem falsified_withEquation (C : ParityClause X) (e : ParityEquation X) (x : X) :
    (C.withEquation e).Falsified x ↔ C.Falsified x ∧ e.Falsified x := by
  simp [withEquation, Falsified, and_comm]

/-- Two clauses are equivalent when they have exactly the same falsifying assignments. -/
def Equivalent (A B : ParityClause X) : Prop :=
  ∀ x, A.Falsified x ↔ B.Falsified x

/-- The affine fiber on which a single parity equation is falsified. -/
def equationFalsifyingAffine (e : ParityEquation X) : AffineSubspace F2 X :=
  (affineSpan F2 ({e.rhs + 1} : Set F2)).comap e.lhs.toAffineMap

@[simp] theorem mem_equationFalsifyingAffine_iff (e : ParityEquation X) (x : X) :
    x ∈ equationFalsifyingAffine e ↔ e.Falsified x := by
  simp [equationFalsifyingAffine, ParityEquation.Falsified]

/-- The common falsifying affine subspace of all equations in a clause. -/
def falsifyingAffine : ParityClause X → AffineSubspace F2 X
  | [] => ⊤
  | e :: C => equationFalsifyingAffine e ⊓ falsifyingAffine C

@[simp] theorem mem_falsifyingAffine_iff (C : ParityClause X) (x : X) :
    x ∈ C.falsifyingAffine ↔ C.Falsified x := by
  induction C with
  | nil => simp [falsifyingAffine, Falsified]
  | cons e C ih =>
      change (x ∈ equationFalsifyingAffine e ∧ x ∈ falsifyingAffine C) ↔
        (e.Falsified x ∧ Falsified C x)
      rw [mem_equationFalsifyingAffine_iff, ih]

instance (C : ParityClause X) (x : X) : Decidable (x ∈ C.falsifyingAffine) :=
  decidable_of_iff (C.Falsified x) (mem_falsifyingAffine_iff C x).symm

@[simp] theorem falsifyingAffine_empty :
    falsifyingAffine ([] : ParityClause X) = ⊤ :=
  rfl

end ParityClause

end Revres
