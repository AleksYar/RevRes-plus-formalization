import Lemma53.BadSelector

/-!
# Part H: final assembly — the Main Lemma (§5-6, §17 of `Lemma53.txt`)

Combines Parts A-G into the affine-to-conical decomposition: `h_A = J_A + E_A` with `J_A` a
degree-`R` conical junta and `E_A ≤ 2^{-κR}`. Lemma A (§4, the "affine mass bound") is taken as a
hypothesis — it is Lemma 5.2 of a separate manuscript, explicitly out of scope here.
-/

namespace Lemma53

variable (N : ℕ)

/-- **Main Lemma** (§5 of `Lemma53.txt`). Given Lemma A (§4) with constant `κ₀ > 0`, every affine
subspace `A ⊆ (F₂³)^N` and every `R` admit a degree-`R` conical junta `J_A` and an error `E_A`
with `h_A = J_A + E_A`, `0 ≤ J_A ≤ h_A ≤ 1`, and `0 ≤ E_A ≤ 2^{-κR}` for `κ = min(κ₀/4, 1/4)`. -/
theorem main_lemma (κ0 : ℝ) (hκ0 : 0 < κ0)
    (lemmaA : ∀ (A : AffineSubspace F2 (V N)), (A : Set (V N)).Nonempty →
      ∀ z : Fin N → F2, density N A z ≤ (2 : ℝ) ^ (-κ0 * (codim N A : ℝ)))
    (R : ℕ) (A : AffineSubspace F2 (V N)) :
    ∃ J E : (Fin N → F2) → ℝ,
      (∀ z, density N A z = J z + E z) ∧
      IsConicalJunta N R J ∧
      (∀ z, 0 ≤ J z ∧ J z ≤ density N A z ∧ density N A z ≤ 1) ∧
      (∀ z, 0 ≤ E z ∧ E z ≤ (2 : ℝ) ^ (-(min (κ0 / 4) (1 / 4)) * (R : ℝ))) := by
  by_cases hA : (A : Set (V N)).Nonempty
  · by_cases hr : R < 4 * codim N A
    · -- Step 1: high codimension (`4r > R`).
      refine ⟨fun _ => 0, density N A, fun z => by ring, isConicalJunta_zero N R,
        fun z => ⟨le_refl 0, density_nonneg N A z, density_le_one N A z⟩,
        fun z => ⟨density_nonneg N A z, ?_⟩⟩
      refine (lemmaA A hA z).trans ?_
      have hr' : (R : ℝ) < 4 * (codim N A : ℝ) := by exact_mod_cast hr
      have hκR : (min (κ0 / 4) (1 / 4)) * (R : ℝ) ≤ κ0 * (codim N A : ℝ) := by
        have h1 : (min (κ0 / 4) (1 / 4)) * (R : ℝ) ≤ (κ0 / 4) * (R : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg R)
        nlinarith [h1, hr']
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hκR])
    · -- `4r ≤ R`: the whole of Parts E-G.
      push Not at hr
      refine ⟨J N A R, Err N A R, density_eq_J_add_Err N A R, isConicalJunta_J N A R,
        fun z => ⟨J_nonneg N A R z, J_le_density N A R z, density_le_one N A z⟩,
        fun z => ⟨Err_nonneg N A R z, ?_⟩⟩
      have ht : 4 * t N A ≤ R := by have := t_le_codim N A; omega
      have hbad := card_bad_le_real N A R ht
      have herr := Err_le_real N A R z
      have hstep : (Nat.card {σ : Fin N → F2 // R < (U N A σ).card} : ℝ) / 2 ^ N
          ≤ (2 : ℝ) ^ (-(R : ℝ) / 4) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ N), mul_comm]
        exact hbad
      refine herr.trans (hstep.trans ?_)
      have hle : (min (κ0 / 4) (1 / 4)) * (R : ℝ) ≤ (R : ℝ) / 4 := by
        have h1 := mul_le_mul_of_nonneg_right (min_le_right (κ0 / 4) (1 / 4))
          (Nat.cast_nonneg R : (0:ℝ) ≤ (R:ℝ))
        linarith [h1]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hle])
  · -- Step 0: `A` empty.
    have hz0 : ∀ z, density N A z = 0 := density_eq_zero_of_empty N hA
    refine ⟨fun _ => 0, fun _ => 0, fun z => by rw [hz0 z]; ring, isConicalJunta_zero N R,
      fun z => ⟨le_refl 0, le_of_eq (hz0 z).symm, by rw [hz0 z]; norm_num⟩,
      fun z => ⟨le_refl 0, Real.rpow_nonneg (by norm_num) _⟩⟩

end Lemma53
