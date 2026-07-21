import Revres.RevRes.Clause
import Mathlib.Data.Multiset.Basic

/-!
# RevRes blackboards

A blackboard is a multiset of parity clauses. This file defines the pointwise number of falsified
clause occurrences and its elementary additive properties.
-/

namespace Revres

open Lemma53

variable {X : Type*} [AddCommGroup X] [Module F2 X]

/-- A blackboard records parity clauses with multiplicity. -/
abbrev Blackboard (X : Type*) [AddCommGroup X] [Module F2 X] := Multiset (ParityClause X)

/-- The natural-number indicator that a clause is falsified at `x`. -/
def falsifiedIndicator (C : ParityClause X) (x : X) : ℕ :=
  if C.Falsified x then 1 else 0

/-- The number of falsified clause occurrences on a blackboard. -/
def falsifiedCount (B : Blackboard X) (x : X) : ℕ :=
  (B.map fun C => falsifiedIndicator C x).sum

@[simp] theorem falsifiedCount_zero (x : X) :
    falsifiedCount (0 : Blackboard X) x = 0 := by
  simp [falsifiedCount]

@[simp] theorem falsifiedCount_singleton (C : ParityClause X) (x : X) :
    falsifiedCount ({C} : Blackboard X) x = falsifiedIndicator C x := by
  simp [falsifiedCount]

theorem falsifiedCount_add (A B : Blackboard X) (x : X) :
    falsifiedCount (A + B) x = falsifiedCount A x + falsifiedCount B x := by
  simp [falsifiedCount]

@[simp] theorem falsifiedIndicator_empty (x : X) :
    falsifiedIndicator ([] : ParityClause X) x = 1 := by
  simp [falsifiedIndicator]

@[simp] theorem falsifiedCount_replicate (q : ℕ) (C : ParityClause X) (x : X) :
    falsifiedCount (Multiset.replicate q C) x = q * falsifiedIndicator C x := by
  simp [falsifiedCount]

@[simp] theorem falsifiedCount_replicate_empty (q : ℕ) (x : X) :
    falsifiedCount (Multiset.replicate q ([] : ParityClause X)) x = q := by
  simp

theorem falsifiedIndicator_eq_affineIndicator (C : ParityClause X) (x : X) :
    falsifiedIndicator C x = if x ∈ C.falsifyingAffine then 1 else 0 := by
  by_cases h : C.Falsified x
  · have hx : x ∈ C.falsifyingAffine :=
      (ParityClause.mem_falsifyingAffine_iff C x).2 h
    simp [falsifiedIndicator, h, hx]
  · have hx : x ∉ C.falsifyingAffine := fun hx =>
      h ((ParityClause.mem_falsifyingAffine_iff C x).1 hx)
    simp [falsifiedIndicator, h, hx]

end Revres
