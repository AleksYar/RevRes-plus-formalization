import Revres.RevRes.Residual
import Mathlib.Data.Multiset.Filter

/-!
# RevRes refutations and canonical residual endpoints

A refutation records an explicit derivation, support of its initial clauses, absence of the empty
clause initially, and presence of the empty clause finally. Common endpoint occurrences are
removed canonically by multiset subtraction.
-/

namespace Revres

open Lemma53

universe u

variable {X : Type u} [AddCommGroup X] [Module F2 X]

noncomputable local instance refutationDecidableEqParityClause :
    DecidableEq (ParityClause X) := Classical.decEq _

/-- An explicit RevRes derivation from supported, nonempty initial clauses to an endpoint
containing the empty clause. -/
structure RevResRefutation (G : Finset (ParityClause X)) where
  initial : Blackboard X
  final : Blackboard X
  derivation : RevDerivation initial final
  initial_supported : ∀ B ∈ initial, B ∈ G
  initial_empty_free : ([] : ParityClause X) ∉ initial
  final_has_empty : ([] : ParityClause X) ∈ final

namespace RevResRefutation

variable {G : Finset (ParityClause X)} (π : RevResRefutation G)

/-- The exact number of recorded reversible steps. -/
def length : ℕ :=
  π.derivation.length

/-- Empty-clause multiplicity in the canonical final residual. -/
noncomputable def emptyMultiplicity : ℕ :=
  (π.final - π.initial).count ([] : ParityClause X)

/-- The nonempty clauses in the canonical final residual, with multiplicity. -/
noncomputable def nonemptyFinalResidual : Blackboard X :=
  (π.final - π.initial).filter fun B => B ≠ []

/-- The final residual is its empty-clause copies plus its nonempty occurrences. -/
theorem finalResidual_eq :
    π.final - π.initial =
      Multiset.replicate π.emptyMultiplicity ([] : ParityClause X) +
        π.nonemptyFinalResidual := by
  classical
  let S : Blackboard X := π.final - π.initial
  change S = Multiset.replicate (S.count []) [] + S.filter (fun B => B ≠ [])
  symm
  rw [← Multiset.filter_eq' S ([] : ParityClause X)]
  exact Multiset.filter_add_not (p := fun B : ParityClause X => B = []) S

/-- At least one empty clause survives endpoint cancellation. -/
theorem one_le_emptyMultiplicity :
    1 ≤ π.emptyMultiplicity := by
  classical
  rw [emptyMultiplicity, Multiset.count_sub,
    Multiset.count_eq_zero_of_notMem π.initial_empty_free, Nat.sub_zero]
  exact (Multiset.count_pos.mpr π.final_has_empty)

/-- The nonempty final residual has at most two occurrences per derivation step. -/
theorem nonemptyFinalResidual_card_le :
    π.nonemptyFinalResidual.card ≤ 2 * π.length := by
  classical
  calc
    π.nonemptyFinalResidual.card ≤ (π.final - π.initial).card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    _ ≤ 2 * π.derivation.length :=
      final_residual_card_le_two_mul_steps π.derivation
    _ = 2 * π.length := rfl

/-- The residual conservation identity with the final empty clauses split off. -/
theorem residual_pointwise :
    ∀ x,
      falsifiedCount (π.initial - π.final) x =
        π.emptyMultiplicity + falsifiedCount π.nonemptyFinalResidual x := by
  intro x
  calc
    falsifiedCount (π.initial - π.final) x =
        falsifiedCount (π.final - π.initial) x :=
      residual_endpoint_identity π.derivation x
    _ = falsifiedCount
        (Multiset.replicate π.emptyMultiplicity ([] : ParityClause X) +
          π.nonemptyFinalResidual) x := by rw [π.finalResidual_eq]
    _ = falsifiedCount
          (Multiset.replicate π.emptyMultiplicity ([] : ParityClause X)) x +
        falsifiedCount π.nonemptyFinalResidual x :=
      falsifiedCount_add _ _ x
    _ = π.emptyMultiplicity + falsifiedCount π.nonemptyFinalResidual x := by
      rw [falsifiedCount_replicate_empty]

end RevResRefutation

end Revres
