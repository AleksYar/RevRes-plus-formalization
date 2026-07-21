import Lemma53.Gadget
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Part B: affine preimage density

Formalizes §2 of `Lemma53.txt`: for an affine subspace `A` of the ambient gadget-block
space `(F₂³)^N`, the density `h_A(z) := |A ∩ Fib(z)| / 4 ^ N`, i.e. the probability that
a uniformly random element of the gadget fiber over `z` lies in `A`.
-/

namespace Lemma53

variable (N : ℕ)

/-- The ambient `F₂`-vector space of `N`-tuples of gadget blocks, i.e. `(F₂³)^N`. -/
abbrev V := Fin N → Block

/-- The codimension of an affine subspace `A ⊆ (F₂³)^N`, i.e. `r` in §6-7 of `Lemma53.txt`. -/
noncomputable def codim (A : AffineSubspace F2 (V N)) : ℕ :=
  Module.finrank F2 (V N) - Module.finrank F2 A.direction

/-- The affine preimage density of `A` at `z`: the fraction of the gadget fiber over `z`
that lies in `A`. -/
noncomputable def density (A : AffineSubspace F2 (V N)) (z : Fin N → F2) : ℝ :=
  ((A : Set (V N)) ∩ gadgetFiber N z).ncard / 4 ^ N

/-- `0 ≤ h_A(z)`. -/
lemma density_nonneg (A : AffineSubspace F2 (V N)) (z : Fin N → F2) :
    0 ≤ density N A z := by
  unfold density
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) N)

/-- `h_A(z) ≤ 1`. -/
lemma density_le_one (A : AffineSubspace F2 (V N)) (z : Fin N → F2) :
    density N A z ≤ 1 := by
  unfold density
  rw [div_le_one (pow_pos (by norm_num) N)]
  have h1 : ((A : Set (V N)) ∩ gadgetFiber N z).ncard ≤ (gadgetFiber N z).ncard :=
    Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
  exact_mod_cast h1.trans_eq (gadgetFiber_ncard N z)

/-- **Step 0.** If `A` is empty, `h_A ≡ 0`. -/
theorem density_eq_zero_of_empty {A : AffineSubspace F2 (V N)} (hA : ¬(A : Set (V N)).Nonempty)
    (z : Fin N → F2) : density N A z = 0 := by
  unfold density
  rw [Set.not_nonempty_iff_eq_empty.mp hA]
  simp

end Lemma53
