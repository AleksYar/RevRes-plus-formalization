import Revres.RevRes.Blackboard

/-!
# Pointwise conservation for reversible resolution

The three local RevRes rules preserve the number of falsified clause occurrences. Additivity then
lifts this equality through an untouched blackboard context and through explicit derivations.
-/

namespace Revres

open Lemma53
open scoped CharTwo

universe u

variable {X : Type u} [AddCommGroup X] [Module F2 X]

/-- One chosen orientation of each reversible local rule. -/
inductive ForwardRule : Blackboard X → Blackboard X → Prop
  | excludedMiddle (lhs : X →ₗ[F2] F2) :
      ForwardRule 0 {([ParityEquation.eqZero lhs, ParityEquation.eqOne lhs] : ParityClause X)}
  | cut (A : ParityClause X) (lhs : X →ₗ[F2] F2) :
      ForwardRule
        ({A.withEquation (ParityEquation.eqZero lhs)} +
          {A.withEquation (ParityEquation.eqOne lhs)})
        {A}
  | equivalence {A B : ParityClause X} (h : A.Equivalent B) :
      ForwardRule {A} {B}

/-- A reversible local rule is a forward rule in either direction. -/
def LocalRule (P Q : Blackboard X) : Prop :=
  ForwardRule P Q ∨ ForwardRule Q P

/-- A full step applies a local rule while carrying an arbitrary context unchanged. -/
def RevStep (B B' : Blackboard X) : Prop :=
  ∃ context premises conclusions,
    B = context + premises ∧
      B' = context + conclusions ∧
      LocalRule premises conclusions

@[simp] theorem excludedMiddle_not_falsified
    (lhs : X →ₗ[F2] F2) (x : X) :
    ¬ ParityClause.Falsified
      ([ParityEquation.eqZero lhs, ParityEquation.eqOne lhs] : ParityClause X) x := by
  rcases F2_eq_zero_or_one (lhs x) with h0 | h1
  · simp [ParityClause.Falsified, ParityEquation.Falsified, ParityEquation.eqZero,
      ParityEquation.eqOne, h0]
  · simp [ParityClause.Falsified, ParityEquation.Falsified, ParityEquation.eqZero,
      ParityEquation.eqOne, h1]

theorem excludedMiddle_conservation (lhs : X →ₗ[F2] F2) (x : X) :
    falsifiedCount (0 : Blackboard X) x =
      falsifiedCount
        ({([ParityEquation.eqZero lhs, ParityEquation.eqOne lhs] : ParityClause X)} :
          Blackboard X)
        x := by
  rw [falsifiedCount_zero, falsifiedCount_singleton]
  simp [falsifiedIndicator]

theorem cut_conservation (A : ParityClause X) (lhs : X →ₗ[F2] F2) (x : X) :
    falsifiedCount
        (({A.withEquation (ParityEquation.eqZero lhs)} : Blackboard X) +
          {A.withEquation (ParityEquation.eqOne lhs)})
        x =
      falsifiedCount ({A} : Blackboard X) x := by
  by_cases hA : A.Falsified x
  · rcases F2_eq_zero_or_one (lhs x) with h0 | h1
    · simp [falsifiedCount, falsifiedIndicator, hA, ParityEquation.Falsified,
        ParityEquation.eqZero, ParityEquation.eqOne, h0]
    · simp [falsifiedCount, falsifiedIndicator, hA, ParityEquation.Falsified,
        ParityEquation.eqZero, ParityEquation.eqOne, h1]
  · simp [falsifiedCount, falsifiedIndicator, hA]

theorem equivalence_conservation {A B : ParityClause X} (h : A.Equivalent B) (x : X) :
    falsifiedCount ({A} : Blackboard X) x = falsifiedCount ({B} : Blackboard X) x := by
  by_cases hA : A.Falsified x
  · have hB : B.Falsified x := (h x).1 hA
    simp [falsifiedIndicator, hA, hB]
  · have hB : ¬ B.Falsified x := fun hBx => hA ((h x).2 hBx)
    simp [falsifiedIndicator, hA, hB]

namespace ForwardRule

theorem falsifiedCount_eq {P Q : Blackboard X} (h : ForwardRule P Q) (x : X) :
    falsifiedCount P x = falsifiedCount Q x := by
  cases h with
  | excludedMiddle lhs => exact excludedMiddle_conservation lhs x
  | cut A lhs => exact cut_conservation A lhs x
  | equivalence h => exact equivalence_conservation h x

end ForwardRule

namespace LocalRule

theorem falsifiedCount_eq {P Q : Blackboard X} (h : LocalRule P Q) (x : X) :
    falsifiedCount P x = falsifiedCount Q x := by
  rcases h with hforward | hreverse
  · exact ForwardRule.falsifiedCount_eq hforward x
  · exact (ForwardRule.falsifiedCount_eq hreverse x).symm

end LocalRule

namespace RevStep

theorem falsifiedCount_eq {B B' : Blackboard X} (h : RevStep B B') (x : X) :
    falsifiedCount B x = falsifiedCount B' x := by
  rcases h with ⟨context, premises, conclusions, rfl, rfl, hlocal⟩
  rw [falsifiedCount_add, falsifiedCount_add, LocalRule.falsifiedCount_eq hlocal x]

end RevStep

/-- An explicit sequence of reversible blackboard steps. -/
inductive RevDerivation (B₀ : Blackboard X) : Blackboard X → Type u
  | refl : RevDerivation B₀ B₀
  | tail {B B' : Blackboard X} :
      RevDerivation B₀ B → RevStep B B' → RevDerivation B₀ B'

namespace RevDerivation

/-- The number of local steps stored in a derivation. -/
def length {B₀ Bₜ : Blackboard X} : RevDerivation B₀ Bₜ → ℕ
  | .refl => 0
  | .tail π _ => π.length + 1

end RevDerivation

/--
Paper correspondence: Section `sec:revres`, Lemma `lem:strong-soundness` in
`revres_xor_superpoly_lower_bound_restriction_notation.tex`.

Mathematical content: Every explicit reversible derivation preserves the
pointwise number of falsified clauses from its initial to its final blackboard.

Formalization note: The paper states conservation for one rule application;
`RevStep.falsifiedCount_eq` is that one-step result, and this theorem iterates it.

Used by: `Revres.static_endpoint_identity`.
-/
theorem derivation_conservation {B₀ Bₜ : Blackboard X} (π : RevDerivation B₀ Bₜ) :
    ∀ x, falsifiedCount B₀ x = falsifiedCount Bₜ x := by
  induction π with
  | refl =>
      intro x
      rfl
  | tail π hstep ih =>
      intro x
      exact (ih x).trans (RevStep.falsifiedCount_eq hstep x)

end Revres
