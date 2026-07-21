import Lemma53.Density
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Field

/-!
# Part D: selector conditioning

Formalizes §7-9 of `Lemma53.txt`: splitting a gadget assignment into selector bits `s` and
data bits `y`, the conditional density `h_{A,σ}`, and the averaging identity
`h_A(z) = 2^{-N} Σ_σ h_{A,σ}(z)`.
-/

namespace Lemma53

variable (N : ℕ)

/-- The data-bit space `y = (u_1, v_1, …, u_N, v_N)`, one `(u_i, v_i)` pair per block. -/
abbrev Y := Fin N → F2 × F2

/-- Reassemble a selector vector `σ` and data vector `y` into a full gadget assignment. -/
def combine (σ : Fin N → F2) (y : Y N) : V N := fun i => (σ i, y i)

/-- The selector part of a gadget assignment. -/
def splitS (X : V N) : Fin N → F2 := fun i => (X i).1

/-- The data part of a gadget assignment. -/
def splitY (X : V N) : Y N := fun i => (X i).2

/-- Splitting and reassembling a gadget assignment recovers it. -/
theorem combine_split (X : V N) : combine N (splitS N X) (splitY N X) = X := rfl

/-- The conditional density `h_{A,σ}(z)`: the fraction of data vectors `y` such that
`(σ, y) ∈ A` and the selected coordinates match `z`. -/
noncomputable def condDensity (A : AffineSubspace F2 (V N)) (σ z : Fin N → F2) : ℝ :=
  ((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)).ncard / 2 ^ N

/-- `0 ≤ h_{A,σ}(z)`. -/
lemma condDensity_nonneg (A : AffineSubspace F2 (V N)) (σ z : Fin N → F2) :
    0 ≤ condDensity N A σ z := by
  unfold condDensity
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) N)

/-- Splitting a gadget assignment set `S` by its selector part partitions `S` into slices,
one per selector vector, each in bijection (via `combine`) with a preimage under `combine`. -/
def sPartitionEquiv (S : Set (V N)) :
    ↥S ≃ Σ _σ : Fin N → F2, ↥((combine N _σ) ⁻¹' S) where
  toFun := fun ⟨X, hX⟩ =>
    ⟨splitS N X, splitY N X, by rw [Set.mem_preimage, combine_split N X]; exact hX⟩
  invFun := fun ⟨σ, y, hy⟩ => ⟨combine N σ y, hy⟩
  left_inv := fun ⟨X, _⟩ => Subtype.ext (combine_split N X)
  right_inv := fun ⟨_σ, _y, _hy⟩ => rfl

/-- The gadget-fiber-affine-mass set `S` splits additively over the selector vector. -/
theorem ncard_eq_sum_ncard_combine_preimage (S : Set (V N)) :
    S.ncard = ∑ σ : Fin N → F2, ((combine N σ) ⁻¹' S).ncard := by
  have h1 : Nat.card ↥S = ∑ σ : Fin N → F2, Nat.card ↥((combine N σ) ⁻¹' S) := by
    rw [Nat.card_congr (sPartitionEquiv N S), Nat.card_sigma]
  simpa [Nat.card_coe_set_eq] using h1

/-- **Selector-averaging identity.** `h_A(z) = 2^{-N} Σ_σ h_{A,σ}(z)`. -/
theorem density_eq_avg_condDensity (A : AffineSubspace F2 (V N)) (z : Fin N → F2) :
    density N A z = (∑ σ : Fin N → F2, condDensity N A σ z) / 2 ^ N := by
  have hcard : ((A : Set (V N)) ∩ gadgetFiber N z).ncard
      = ∑ σ : Fin N → F2, ((combine N σ) ⁻¹' ((A : Set (V N)) ∩ gadgetFiber N z)).ncard :=
    ncard_eq_sum_ncard_combine_preimage N _
  have hsum : (∑ σ : Fin N → F2, condDensity N A σ z)
      = (((A : Set (V N)) ∩ gadgetFiber N z).ncard : ℝ) / 2 ^ N := by
    simp only [condDensity, ← Finset.sum_div]
    congr 1
    exact_mod_cast hcard.symm
  have h4 : (4:ℝ) ^ N = (2:ℝ) ^ N * (2:ℝ) ^ N := by
    rw [← mul_pow]; norm_num
  unfold density
  rw [h4, ← div_div, ← hsum]

end Lemma53
