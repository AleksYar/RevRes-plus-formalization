import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Part A: the 3-bit indexing gadget

This file formalizes §1 of `Lemma53.txt`: the gadget `g : F₂³ → F₂`, its blockwise
fiber cardinality `4`, and the `N`-fold gadget fiber cardinality `4 ^ N`.
-/

namespace Lemma53

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-- The base field `F₂ = {0, 1}`. -/
abbrev F2 := ZMod 2

/-- `F₂` has exactly two elements, `0` and `1`. -/
theorem F2_eq_zero_or_one : ∀ x : F2, x = 0 ∨ x = 1 := by decide

/-- Over `F₂`, `x ≠ 0` is the same as `x = 1`. -/
theorem F2_ne_zero_iff_eq_one {x : F2} : x ≠ 0 ↔ x = 1 :=
  ⟨(F2_eq_zero_or_one x).resolve_left, fun h => h ▸ one_ne_zero⟩

/-- The 3-bit indexing gadget: `g(s, u, v) = u` if `s = 0`, and `v` if `s = 1`. -/
def gadget (s u v : F2) : F2 := if s = 0 then u else v

/-- Equivalent affine form `g(s, u, v) = (1 - s) u + s v`, as in the source proof. -/
lemma gadget_eq_affine (s u v : F2) : gadget s u v = (1 - s) * u + s * v := by
  fin_cases s <;> fin_cases u <;> fin_cases v <;> decide

/-- A single gadget block: a selector bit together with two data bits `(s, u, v)`. -/
abbrev Block := F2 × F2 × F2

/-- Evaluate the gadget on a block. -/
def blockEval (t : Block) : F2 := gadget t.1 t.2.1 t.2.2

/-- The fiber of the single-block gadget over an output bit `b` has exactly `4` elements. -/
lemma blockFiber_card (b : F2) : Fintype.card {t : Block // blockEval t = b} = 4 := by
  fin_cases b <;> decide

variable (N : ℕ)

/-- Apply the gadget blockwise to an `N`-tuple of gadget blocks. -/
def gadgetN (X : Fin N → Block) : Fin N → F2 := fun i => blockEval (X i)

/-- The gadget fiber over `z`: all block-tuples whose blockwise gadget evaluation is `z`. -/
def gadgetFiber (z : Fin N → F2) : Set (Fin N → Block) := {X | gadgetN N X = z}

/-- The gadget fiber over `z` is equivalent to the product, over each block `i`, of the
single-block fiber over `z i`. -/
def gadgetFiberEquiv (z : Fin N → F2) :
    gadgetFiber N z ≃ ∀ i : Fin N, {t : Block // blockEval t = z i} :=
  (Equiv.subtypeEquivRight (fun X => by
    simp only [gadgetFiber, Set.mem_setOf_eq, gadgetN, funext_iff])).trans
    Equiv.subtypePiEquivPi

noncomputable instance (z : Fin N → F2) : Fintype (gadgetFiber N z) :=
  Fintype.ofEquiv _ (gadgetFiberEquiv N z).symm

/-- **Fiber cardinality.** Every gadget fiber over `z ∈ F₂^N` has exactly `4 ^ N` elements. -/
theorem gadgetFiber_card (z : Fin N → F2) :
    Fintype.card (gadgetFiber N z) = 4 ^ N := by
  rw [Fintype.card_congr (gadgetFiberEquiv N z), Fintype.card_pi]
  simp [blockFiber_card]

/-- `Set.ncard` version of `gadgetFiber_card`, used when working with `Set` intersections. -/
theorem gadgetFiber_ncard (z : Fin N → F2) :
    (gadgetFiber N z).ncard = 4 ^ N := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, gadgetFiber_card]

end Lemma53
