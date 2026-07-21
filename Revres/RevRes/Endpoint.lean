import Revres.RevRes.Conservation

/-!
# Static endpoint identities

Conservation and the universal falsification of the empty clause give the pointwise endpoint
identity. An indexed form expands initial clause multiplicities explicitly.
-/

namespace Revres

open Lemma53

universe u v

variable {X : Type u} [AddCommGroup X] [Module F2 X]

/-- Conservation specialized to a final blackboard containing `q` empty clauses and a residual
multiset. -/
theorem static_endpoint_identity {B₀ Bₜ R : Blackboard X} {q : ℕ}
    (π : RevDerivation B₀ Bₜ)
    (hfinal : Bₜ = Multiset.replicate q ([] : ParityClause X) + R) :
    ∀ x, falsifiedCount B₀ x = q + falsifiedCount R x := by
  intro x
  calc
    falsifiedCount B₀ x = falsifiedCount Bₜ x := derivation_conservation π x
    _ = falsifiedCount (Multiset.replicate q ([] : ParityClause X) + R) x := by rw [hfinal]
    _ = falsifiedCount (Multiset.replicate q ([] : ParityClause X)) x +
        falsifiedCount R x := falsifiedCount_add _ _ x
    _ = q + falsifiedCount R x := by rw [falsifiedCount_replicate_empty]

/-- The initial blackboard with clause `D i` occurring with multiplicity `α i`. -/
def blackboardOfMultiplicities {ι : Type v} [Fintype ι]
    (D : ι → ParityClause X) (α : ι → ℕ) : Blackboard X :=
  ∑ i, Multiset.replicate (α i) (D i)

theorem falsifiedCount_blackboardOfMultiplicities {ι : Type v} [Fintype ι]
    (D : ι → ParityClause X) (α : ι → ℕ) (x : X) :
    falsifiedCount (blackboardOfMultiplicities D α) x =
      ∑ i, α i * falsifiedIndicator (D i) x := by
  classical
  let countHom : Blackboard X →+ ℕ :=
    { toFun := fun B => falsifiedCount B x
      map_zero' := falsifiedCount_zero x
      map_add' := fun A B => falsifiedCount_add A B x }
  change countHom (∑ i, Multiset.replicate (α i) (D i)) = _
  rw [map_sum]
  simp [countHom]

/-- The manuscript-style endpoint identity with indexed initial multiplicities. -/
theorem static_endpoint_identity_indexed {ι : Type v} [Fintype ι]
    {Bₜ R : Blackboard X} {q : ℕ}
    (D : ι → ParityClause X) (α : ι → ℕ)
    (π : RevDerivation (blackboardOfMultiplicities D α) Bₜ)
    (hfinal : Bₜ = Multiset.replicate q ([] : ParityClause X) + R) :
    ∀ x, (∑ i, α i * falsifiedIndicator (D i) x) = q + falsifiedCount R x := by
  intro x
  calc
    (∑ i, α i * falsifiedIndicator (D i) x) =
        falsifiedCount (blackboardOfMultiplicities D α) x :=
      (falsifiedCount_blackboardOfMultiplicities D α x).symm
    _ = q + falsifiedCount R x := static_endpoint_identity π hfinal x

end Revres
