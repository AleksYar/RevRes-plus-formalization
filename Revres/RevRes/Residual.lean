import Revres.RevRes.Endpoint
import Mathlib.Data.Multiset.UnionInter

/-!
# Residual endpoints

This file canonically cancels common clause multiplicities at the endpoints of a RevRes
derivation. It proves pointwise conservation for the residual endpoints and an exact bound of two
new surviving final clauses per derivation step.
-/

namespace Revres

open Lemma53

universe u v

variable {X : Type u} [AddCommGroup X] [Module F2 X]

noncomputable local instance residualDecidableEqParityClause :
    DecidableEq (ParityClause X) := Classical.decEq _

/-- Initial clause occurrences left after cancelling the final endpoint. -/
noncomputable def initialResidual (B₀ Bₜ : Blackboard X) : Blackboard X :=
  B₀ - Bₜ

/-- Final clause occurrences left after cancelling the initial endpoint. -/
noncomputable def finalResidual (B₀ Bₜ : Blackboard X) : Blackboard X :=
  Bₜ - B₀

/-- Cancelling common endpoint multiplicities preserves the pointwise falsified count identity. -/
theorem residual_endpoint_identity {B₀ Bₜ : Blackboard X} (π : RevDerivation B₀ Bₜ) :
    ∀ x, falsifiedCount (B₀ - Bₜ) x = falsifiedCount (Bₜ - B₀) x := by
  intro x
  have hcons : falsifiedCount B₀ x = falsifiedCount Bₜ x :=
    derivation_conservation π x
  have hleft :
      falsifiedCount B₀ x =
        falsifiedCount (B₀ - Bₜ) x + falsifiedCount (B₀ ∩ Bₜ) x := by
    calc
      falsifiedCount B₀ x = falsifiedCount ((B₀ - Bₜ) + B₀ ∩ Bₜ) x :=
        congrArg (fun B => falsifiedCount B x) (Multiset.sub_add_inter B₀ Bₜ).symm
      _ = falsifiedCount (B₀ - Bₜ) x + falsifiedCount (B₀ ∩ Bₜ) x :=
        falsifiedCount_add _ _ x
  have hright :
      falsifiedCount Bₜ x =
        falsifiedCount (Bₜ - B₀) x + falsifiedCount (B₀ ∩ Bₜ) x := by
    calc
      falsifiedCount Bₜ x = falsifiedCount ((Bₜ - B₀) + Bₜ ∩ B₀) x :=
        congrArg (fun B => falsifiedCount B x) (Multiset.sub_add_inter Bₜ B₀).symm
      _ = falsifiedCount (Bₜ - B₀) x + falsifiedCount (Bₜ ∩ B₀) x :=
        falsifiedCount_add _ _ x
      _ = falsifiedCount (Bₜ - B₀) x + falsifiedCount (B₀ ∩ Bₜ) x := by
        rw [Multiset.inter_comm Bₜ B₀]
  exact Nat.add_right_cancel (hleft.symm.trans (hcons.trans hright))

namespace LocalRule

/-- Either side of a reversible local rule, in particular its right side, has at most two clause
occurrences. -/
theorem right_card_le_two {P Q : Blackboard X} (h : LocalRule P Q) : Q.card ≤ 2 := by
  rcases h with hforward | hreverse
  · cases hforward <;> simp
  · cases hreverse <;> simp

end LocalRule

/-- Adding `C` before subtracting `S` leaves no more occurrences than subtracting first and then
adding all of `C`. -/
theorem sub_add_sub_le {α : Type v} [DecidableEq α] (A S C : Multiset α) :
    (A + C) - S ≤ (A - S) + C := by
  rw [Multiset.sub_le_iff_le_add']
  simpa [Multiset.add_assoc] using
    (Multiset.add_le_add_right (Multiset.le_add_sub (s := A) (t := S)) :
      A + C ≤ (S + (A - S)) + C)

/-- Cardinality form of `sub_add_sub_le`. -/
theorem card_sub_le_card_sub_add {α : Type v} [DecidableEq α] (A S C : Multiset α) :
    ((A + C) - S).card ≤ (A - S).card + C.card := by
  rw [← Multiset.card_add]
  exact Multiset.card_le_card (sub_add_sub_le A S C)

namespace RevStep

/-- One RevRes step creates at most two additional final occurrences surviving subtraction by a
fixed initial blackboard. -/
theorem finalResidual_card_le {B₀ B B' : Blackboard X} (hstep : RevStep B B') :
    (B' - B₀).card ≤ (B - B₀).card + 2 := by
  rcases hstep with ⟨context, premises, conclusions, rfl, rfl, hlocal⟩
  have hcontext :
      (context - B₀).card ≤ ((context + premises) - B₀).card :=
    Multiset.card_le_card
      (Multiset.sub_le_sub_right (Multiset.le_add_right context premises))
  calc
    ((context + conclusions) - B₀).card ≤
        (context - B₀).card + conclusions.card :=
      card_sub_le_card_sub_add context B₀ conclusions
    _ ≤ ((context + premises) - B₀).card + conclusions.card :=
      Nat.add_le_add_right hcontext conclusions.card
    _ ≤ ((context + premises) - B₀).card + 2 :=
      Nat.add_le_add_left (LocalRule.right_card_le_two hlocal) _

end RevStep

/-- The final residual contains at most two clause occurrences per derivation step. -/
theorem final_residual_card_le_two_mul_steps {B₀ Bₜ : Blackboard X}
    (π : RevDerivation B₀ Bₜ) :
    (Bₜ - B₀).card ≤ 2 * π.length := by
  induction π with
  | refl => simp [RevDerivation.length]
  | tail π hstep ih =>
      calc
        (_ - B₀).card ≤ (_ - B₀).card + 2 :=
          RevStep.finalResidual_card_le hstep
        _ ≤ 2 * π.length + 2 := Nat.add_le_add_right ih 2
        _ = 2 * (π.length + 1) := by simp [Nat.mul_add]

/-- Pointwise conservation and the exact size bound for the canonical residual endpoints. -/
theorem residual_endpoint_package {B₀ Bₜ : Blackboard X} (π : RevDerivation B₀ Bₜ) :
    (∀ x, falsifiedCount (B₀ - Bₜ) x = falsifiedCount (Bₜ - B₀) x) ∧
      (Bₜ - B₀).card ≤ 2 * π.length :=
  ⟨residual_endpoint_identity π, final_residual_card_le_two_mul_steps π⟩

end Revres
