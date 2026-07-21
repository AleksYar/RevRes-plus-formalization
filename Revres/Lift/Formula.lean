import Revres.Lift.Clause
import Mathlib.Data.Finset.Union

/-!
# Truth-table lift of a CNF

The full index lift is the union of the parity-clause conversions of every lifted base clause.
-/

namespace Revres

open Lemma53

universe u

variable {N : ℕ}

noncomputable local instance liftFormulaDecidableEqParityClause
    {X : Type u} [AddCommGroup X] [Module F2 X] : DecidableEq (ParityClause X) :=
  Classical.decEq _

/-- Semantic unsatisfiability for a finite set of parity clauses. -/
noncomputable def RevresUnsat {X : Type u} [AddCommGroup X] [Module F2 X]
    (G : Finset (ParityClause X)) : Prop :=
  ∀ x : X, ∃ D ∈ G, D.Falsified x

/-- Lift every base clause through the index gadget and convert the results to parity clauses. -/
noncomputable def indexLift (F : CNF N) : Finset (ParityClause (V N)) :=
  F.biUnion fun C => (liftClause C).image LiftedClause.toParityClause

theorem mem_indexLift_iff (F : CNF N) (D : ParityClause (V N)) :
    D ∈ indexLift F ↔
      ∃ C ∈ F, ∃ L ∈ liftClause C, L.toParityClause = D := by
  classical
  simp [indexLift]

/-- Truth-table lifting through the index gadget preserves semantic unsatisfiability. -/
theorem indexLift_unsat {F : CNF N} (hF : F.Unsat) :
    RevresUnsat (indexLift F) := by
  intro X
  rcases hF (gadgetN N X) with ⟨C, hCF, hCfalse⟩
  rcases (exists_falsified_mem_liftClause_iff C X).2 hCfalse with ⟨L, hLlift, hLfalse⟩
  refine ⟨L.toParityClause, (mem_indexLift_iff F L.toParityClause).2 ?_, ?_⟩
  · exact ⟨C, hCF, L, hLlift, rfl⟩
  · exact (LiftedClause.toParityClause_falsified_iff L X).2 hLfalse

end Revres
