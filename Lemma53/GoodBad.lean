import Lemma53.Claim1
import Lemma53.Junta

/-!
# Part F: the `J_A` / `E_A` decomposition

Formalizes §12-13 of `Lemma53.txt`: splitting the selector average into good selectors
(`|U_σ| ≤ R`) and bad selectors, giving `h_A = J_A + E_A` with `0 ≤ J_A ≤ h_A` and `J_A` a
degree-`R` conical junta.
-/

namespace Lemma53

variable (N : ℕ)

/-- A selector `σ` is good (for a given target degree `R`) if `|U_σ| ≤ R`. -/
def good (A : AffineSubspace F2 (V N)) (R : ℕ) (σ : Fin N → F2) : Prop :=
  (U N A σ).card ≤ R

noncomputable instance (A : AffineSubspace F2 (V N)) (R : ℕ) (σ : Fin N → F2) :
    Decidable (good N A R σ) := by unfold good; infer_instance

/-- `J_A(z) := 2^{-N} Σ_σ 1[good σ] h_{A,σ}(z)`. -/
noncomputable def J (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) : ℝ :=
  (∑ σ : Fin N → F2, if good N A R σ then condDensity N A σ z else 0) / 2 ^ N

/-- `E_A(z) := 2^{-N} Σ_σ 1[¬ good σ] h_{A,σ}(z)`. -/
noncomputable def Err (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) : ℝ :=
  (∑ σ : Fin N → F2, if good N A R σ then 0 else condDensity N A σ z) / 2 ^ N

/-- **`h_A = J_A + E_A`.** -/
theorem density_eq_J_add_Err (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) :
    density N A z = J N A R z + Err N A R z := by
  rw [density_eq_avg_condDensity, J, Err, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : good N A R σ <;> simp [h]

/-- `0 ≤ J_A(z)`. -/
theorem J_nonneg (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) : 0 ≤ J N A R z := by
  unfold J
  apply div_nonneg _ (pow_nonneg (by norm_num) N)
  apply Finset.sum_nonneg
  intro σ _
  split
  · exact condDensity_nonneg N A σ z
  · exact le_refl 0

/-- `E_A(z) ≥ 0`. -/
theorem Err_nonneg (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) : 0 ≤ Err N A R z := by
  unfold Err
  apply div_nonneg _ (pow_nonneg (by norm_num) N)
  apply Finset.sum_nonneg
  intro σ _
  split
  · exact le_refl 0
  · exact condDensity_nonneg N A σ z

/-- `J_A(z) ≤ h_A(z)`. -/
theorem J_le_density (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) :
    J N A R z ≤ density N A z := by
  rw [density_eq_J_add_Err N A R z]
  linarith [Err_nonneg N A R z]

/-- **`J_A` is a degree-`R` conical junta.** -/
theorem isConicalJunta_J (A : AffineSubspace F2 (V N)) (R : ℕ) :
    IsConicalJunta N R (J N A R) := by
  classical
  have hterm : ∀ σ : Fin N → F2, IsConicalJunta N R
      (fun z => (if good N A R σ then condDensity N A σ z else 0) / 2 ^ N) := by
    intro σ
    have hraw : IsConicalJunta N R
        (fun z => if good N A R σ then condDensity N A σ z else 0) := by
      by_cases h : good N A R σ
      · simpa only [h, if_true] using
          isConicalJunta_of_dependsOn N h (condDensity_dependsOn N A σ)
            (condDensity_nonneg N A σ)
      · simpa only [h, if_false] using isConicalJunta_zero N R
    have hscaled := isConicalJunta_const_mul N
      (c := ((2:ℝ) ^ N)⁻¹) (inv_nonneg.mpr (pow_nonneg (by norm_num) N)) hraw
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hcombo := isConicalJunta_sum N (c := fun _ : Fin N → F2 => (1:ℝ))
    (fun _ => zero_le_one) hterm
  have heq : J N A R = fun z => ∑ σ : Fin N → F2,
      (1:ℝ) * ((if good N A R σ then condDensity N A σ z else 0) / 2 ^ N) := by
    funext z
    unfold J
    rw [Finset.sum_div]
    simp
  rw [heq]
  exact hcombo

end Lemma53
