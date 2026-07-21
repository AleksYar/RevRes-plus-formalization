import Lemma53.Claim1
import Lemma53.GoodBad
import Lemma53.LinearAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Part G: the bad-selector estimate

Formalizes §14-16 of `Lemma53.txt` (Claims 3-5): if `σ` is bad (`|U_σ| > R`), some `w ∈ W_σ` has
wide block support; a fixed wide `w` is rarely in `E_σ`; combined with a union bound over `L`,
few selectors are bad when `4 * t ≤ R`.
-/

namespace Lemma53

variable (N : ℕ)

/-- Evaluate a data vector at the `σ`-selected coordinate of block `i`. -/
def evalAt (σ : Fin N → F2) (i : Fin N) : Y N →ₗ[F2] F2 :=
  (LinearMap.proj i).comp (selPick N σ)

theorem evalAt_apply (σ : Fin N → F2) (i : Fin N) (y : Y N) :
    evalAt N σ i y = selPick N σ y i := rfl

theorem selPick_comp_selSpread (σ : Fin N → F2) (q : Fin N → F2) :
    selPick N σ (selSpread N σ q) = q := by
  funext i
  simp only [selPick_apply, selSpread]
  by_cases h : σ i = 0 <;> simp [h]

/-- For `y` in the selected-coordinate subspace `E_σ`, the block support of `y` is exactly the
set of blocks where the selected coordinate is nonzero. -/
theorem blockSupport_eq_filter_selPick_of_mem_E (σ : Fin N → F2) {y : Y N} (hy : y ∈ E N σ) :
    blockSupport N y = Finset.univ.filter (fun i => selPick N σ y i ≠ 0) := by
  obtain ⟨q, rfl⟩ := hy
  rw [selPick_comp_selSpread, blockSupport_selSpread]

/-- The evaluation functional on `W_σ`, restricted from `evalAt`. -/
noncomputable def φ (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) (i : Fin N) :
    W N A σ →ₗ[F2] F2 :=
  (evalAt N σ i).comp (W N A σ).subtype

theorem φ_apply (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) (i : Fin N) (w : W N A σ) :
    φ N A σ i w = selPick N σ (w : Y N) i := rfl

/-- A block `i` is in the support of `w ∈ W_σ` iff the evaluation functional at `i` is nonzero
on `w`. -/
theorem mem_blockSupport_iff_φ_ne_zero (A : AffineSubspace F2 (V N)) (σ : Fin N → F2)
    (i : Fin N) (w : W N A σ) :
    i ∈ blockSupport N (w : Y N) ↔ φ N A σ i w ≠ 0 := by
  have hwE : (w : Y N) ∈ E N σ := (Submodule.mem_inf.mp w.2).2
  rw [blockSupport_eq_filter_selPick_of_mem_E N σ hwE, φ_apply]
  simp

/-- `i ∈ U_σ` iff the evaluation functional at `i` is nonzero on `W_σ`. -/
theorem mem_U_iff_φ_ne_zero (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) (i : Fin N) :
    i ∈ U N A σ ↔ φ N A σ i ≠ 0 := by
  classical
  unfold U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show (∃ w : W N A σ, i ∈ blockSupport N (w : Y N))
      ↔ ∃ w : W N A σ, φ N A σ i w ≠ 0 from
    exists_congr (fun w => mem_blockSupport_iff_φ_ne_zero N A σ i w)]
  constructor
  · rintro ⟨w, hw⟩ hφ0
    exact hw (by rw [hφ0]; rfl)
  · intro hφ0
    by_contra hcontra
    push Not at hcontra
    apply hφ0
    ext w
    simp [hcontra w]

/-- **Double-counting identity.** Twice the total block-support size over `W_σ` equals
`|U_σ| · |W_σ|`. -/
theorem sum_blockSupport_eq (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) :
    2 * ∑ w : W N A σ, (blockSupport N (w : Y N)).card
      = (U N A σ).card * Nat.card (W N A σ) := by
  classical
  have hblock : ∀ w : W N A σ, blockSupport N (w : Y N)
      = Finset.univ.filter (fun i => φ N A σ i w = 1) := by
    intro w
    have hwE : (w : Y N) ∈ E N σ := (Submodule.mem_inf.mp w.2).2
    rw [blockSupport_eq_filter_selPick_of_mem_E N σ hwE]
    ext i
    simp [φ_apply, F2_ne_zero_iff_eq_one]
  have hfiberCard : ∀ i : Fin N,
      Nat.card {w : W N A σ // φ N A σ i w = 1}
        = (Finset.univ.filter (fun w : W N A σ => φ N A σ i w = 1)).card := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc 2 * ∑ w : W N A σ, (blockSupport N (w : Y N)).card
      = 2 * ∑ w : W N A σ, ∑ i : Fin N, (if φ N A σ i w = 1 then 1 else 0) := by
        congr 1
        exact Finset.sum_congr rfl fun w _ => by rw [hblock w, Finset.card_filter]
    _ = 2 * ∑ i : Fin N, ∑ w : W N A σ, (if φ N A σ i w = 1 then 1 else 0) := by
        rw [Finset.sum_comm]
    _ = 2 * ∑ i : Fin N, (Finset.univ.filter (fun w : W N A σ => φ N A σ i w = 1)).card := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.card_filter]
    _ = ∑ i : Fin N, 2 * (Finset.univ.filter (fun w : W N A σ => φ N A σ i w = 1)).card := by
        rw [Finset.mul_sum]
    _ = ∑ i : Fin N, if i ∈ U N A σ then Nat.card (W N A σ) else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hfiberCard]
        by_cases h : i ∈ U N A σ
        · simp only [h, if_true]
          exact card_functional_eq_one ((mem_U_iff_φ_ne_zero N A σ i).mp h)
        · simp only [h, if_false]
          have hφ0 : φ N A σ i = 0 := by
            by_contra hc
            exact h ((mem_U_iff_φ_ne_zero N A σ i).mpr hc)
          haveI : IsEmpty {w : W N A σ // φ N A σ i w = 1} :=
            ⟨fun ⟨w, hw⟩ => by rw [hφ0] at hw; simp at hw⟩
          simp
    _ = ∑ i ∈ U N A σ, Nat.card (W N A σ) := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp
    _ = (U N A σ).card * Nat.card (W N A σ) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Claim 3.** If `|U_σ| > R`, some nonzero `w ∈ W_σ` has `2 · |bsupp(w)| > R`. -/
theorem exists_wide_of_card_U_gt (A : AffineSubspace F2 (V N)) (σ : Fin N → F2) (R : ℕ)
    (hR : R < (U N A σ).card) :
    ∃ w : W N A σ, w ≠ 0 ∧ R < 2 * (blockSupport N (w : Y N)).card := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hle : ∀ w : W N A σ, 2 * (blockSupport N (w : Y N)).card ≤ R := by
    intro w
    by_cases hw : w = 0
    · have hw0 : (w : Y N) = 0 := by rw [hw]; rfl
      have hempty : blockSupport N (w : Y N) = ∅ := by
        rw [hw0]
        apply Finset.filter_false_of_mem
        intro i _
        simp only [Pi.zero_apply, not_not]
        decide
      simp [hempty]
    · exact hcontra w hw
  have hsum_le : 2 * ∑ w : W N A σ, (blockSupport N (w : Y N)).card
      ≤ R * Nat.card (W N A σ) := by
    calc 2 * ∑ w : W N A σ, (blockSupport N (w : Y N)).card
        = ∑ w : W N A σ, 2 * (blockSupport N (w : Y N)).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _w : W N A σ, R := Finset.sum_le_sum fun w _ => hle w
      _ = Fintype.card (W N A σ) * R := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      _ = R * Nat.card (W N A σ) := by rw [Nat.card_eq_fintype_card]; ring
  rw [sum_blockSupport_eq] at hsum_le
  have hWpos : 0 < Nat.card (W N A σ) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have : (U N A σ).card ≤ R := Nat.le_of_mul_le_mul_right hsum_le hWpos
  omega

/-- The forced selector value at a block in the support of `w` (arbitrary elsewhere). -/
def target (w : Y N) (i : Fin N) : F2 := if (w i).1 ≠ 0 then 0 else 1

/-- If `w ∈ E_σ`, then `σ` is forced to `target w` on every block of `bsupp(w)`. -/
theorem mem_E_imp_forced (w : Y N) (σ : Fin N → F2) (h : w ∈ E N σ) :
    ∀ i ∈ blockSupport N w, σ i = target N w i := by
  obtain ⟨q, rfl⟩ := h
  intro i hi
  simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hval : selSpread N σ q i = if σ i = 0 then (q i, 0) else (0, q i) := rfl
  rw [hval] at hi
  unfold target
  rw [hval]
  by_cases hσ : σ i = 0
  · have hq : q i ≠ 0 := by
      intro hq0
      apply hi
      rw [hq0]
      split <;> rfl
    simp [hσ, hq]
  · have hσ1 : σ i = 1 := F2_ne_zero_iff_eq_one.mp hσ
    have hq : q i ≠ 0 := by
      intro hq0
      apply hi
      rw [hq0]
      split <;> rfl
    simp [hσ1]

/-- **Claim 4 (upper bound).** For any `w : Y N`, the number of selectors `σ` with `w ∈ E_σ` is
at most `2 ^ (N - |bsupp(w)|)`. -/
theorem card_sigma_mem_E_le (w : Y N) :
    Nat.card {σ : Fin N → F2 // w ∈ E N σ} ≤ 2 ^ (N - (blockSupport N w).card) := by
  rw [← card_cube N (blockSupport N w) (target N w)]
  apply Nat.card_le_card_of_injective (f := fun σ => (⟨σ.1, mem_E_imp_forced N w σ.1 σ.2⟩ :
    {z : Fin N → F2 // ∀ i ∈ blockSupport N w, z i = target N w i}))
  intro σ1 σ2 heq
  simp only [Subtype.mk.injEq] at heq
  exact Subtype.ext heq

open Classical in
/-- **Union bound (nat/Finset form).** The bad selectors are covered by the union, over wide
`w ∈ L`, of the selectors putting `w` in `E_σ`. -/
theorem card_bad_le_sum (A : AffineSubspace F2 (V N)) (R : ℕ) :
    (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card)).card
      ≤ ∑ w ∈ (Finset.univ : Finset (rowspanL N A)).filter
          (fun w : rowspanL N A => w ≠ 0 ∧ R < 2 * (blockSupport N (w : Y N)).card),
        (Finset.univ.filter (fun σ' : Fin N → F2 => (w : Y N) ∈ E N σ')).card := by
  classical
  have hsub : (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card))
      ⊆ ((Finset.univ : Finset (rowspanL N A)).filter
          (fun w : rowspanL N A => w ≠ 0 ∧ R < 2 * (blockSupport N (w : Y N)).card)).biUnion
        (fun w : rowspanL N A => Finset.univ.filter
          (fun σ' : Fin N → F2 => (w : Y N) ∈ E N σ')) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨w, hw0, hwR⟩ := exists_wide_of_card_U_gt N A σ R hσ
    have hwL : (w : Y N) ∈ rowspanL N A := (Submodule.mem_inf.mp w.2).1
    have hwE : (w : Y N) ∈ E N σ := (Submodule.mem_inf.mp w.2).2
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨(w : Y N), hwL⟩, ⟨?_, hwR⟩, hwE⟩
    intro hc
    apply hw0
    apply Subtype.ext
    have hval : (w : Y N) = 0 := by simpa using congrArg Subtype.val hc
    simpa using hval
  calc (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le

private theorem two_pow_sub_eq {a b : ℕ} (h : b ≤ a) :
    (2 : ℝ) ^ (a - b) = (2 : ℝ) ^ a / (2 : ℝ) ^ b := by
  rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel h]

/-- Each term of the union bound, for a wide `w`, is at most `2^N · 2^{-R/2}`. -/
theorem term_le (A : AffineSubspace F2 (V N)) (R : ℕ) {w : rowspanL N A}
    (hwR : R < 2 * (blockSupport N (w : Y N)).card) :
    (Nat.card {σ' : Fin N → F2 // (w : Y N) ∈ E N σ'} : ℝ)
      ≤ (2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 2) := by
  have hle : Nat.card {σ' : Fin N → F2 // (w : Y N) ∈ E N σ'}
      ≤ 2 ^ (N - (blockSupport N (w : Y N)).card) := card_sigma_mem_E_le N (w : Y N)
  have hcastle : (Nat.card {σ' : Fin N → F2 // (w : Y N) ∈ E N σ'} : ℝ)
      ≤ (2 : ℝ) ^ (N - (blockSupport N (w : Y N)).card) := by exact_mod_cast hle
  refine hcastle.trans ?_
  have hkN : (blockSupport N (w : Y N)).card ≤ N := by
    have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => w.1 i ≠ (0, 0))
    simpa [blockSupport, Finset.card_univ] using h1
  rw [two_pow_sub_eq hkN, div_le_iff₀ (by positivity)]
  have hR' : (R : ℝ) < 2 * (blockSupport N (w : Y N)).card := by exact_mod_cast hwR
  have hexp : -(R : ℝ) / 2 + (blockSupport N (w : Y N)).card ≥ 0 := by linarith
  have hstep : (1 : ℝ) ≤ (2 : ℝ) ^ (-(R : ℝ) / 2 + (blockSupport N (w : Y N)).card) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (-(R : ℝ) / 2 + (blockSupport N (w : Y N)).card) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast] at hstep
  nlinarith [hstep, (by positivity : (0:ℝ) < (2:ℝ) ^ N)]

open Classical in
/-- **Claim 5.** When `4 · t ≤ R`, the fraction of bad selectors is at most `2^{-R/4}`. -/
theorem card_bad_le_real (A : AffineSubspace F2 (V N)) (R : ℕ) (hR : 4 * t N A ≤ R) :
    (Nat.card {σ : Fin N → F2 // R < (U N A σ).card} : ℝ)
      ≤ (2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 4) := by
  set S := (Finset.univ : Finset (rowspanL N A)).filter
    (fun w : rowspanL N A => w ≠ 0 ∧ R < 2 * (blockSupport N (w : Y N)).card) with hSdef
  have hcard_eq : Nat.card {σ : Fin N → F2 // R < (U N A σ).card}
      = (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hnat := card_bad_le_sum N A R
  have hstep1 : (Nat.card {σ : Fin N → F2 // R < (U N A σ).card} : ℝ)
      ≤ (∑ w ∈ S, (Finset.univ.filter (fun σ' : Fin N → F2 => (w : Y N) ∈ E N σ')).card : ℝ) := by
    rw [hcard_eq]; exact_mod_cast hnat
  refine hstep1.trans ?_
  have hstep2 : (∑ w ∈ S, (Finset.univ.filter (fun σ' : Fin N → F2 => (w : Y N) ∈ E N σ')).card : ℝ)
      ≤ ∑ _w ∈ S, (2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 2) := by
    apply Finset.sum_le_sum
    intro w hw
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hcardfin : ((Finset.univ.filter (fun σ' : Fin N → F2 => (w : Y N) ∈ E N σ')).card : ℝ)
        = (Nat.card {σ' : Fin N → F2 // (w : Y N) ∈ E N σ'} : ℝ) := by
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcardfin]
    exact term_le N A R hw.2
  refine hstep2.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hScard : S.card ≤ 2 ^ (t N A) := by
    calc S.card ≤ (Finset.univ : Finset (rowspanL N A)).card := Finset.card_filter_le _ _
      _ = Nat.card (rowspanL N A) := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
      _ = 2 ^ (t N A) := nat_card_eq_two_pow_finrank
  have hScard' : (S.card : ℝ) ≤ (2 : ℝ) ^ (t N A) := by exact_mod_cast hScard
  have htR : (t N A : ℝ) ≤ (R : ℝ) / 4 := by
    have h4 : (4 * t N A : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hScardR : (S.card : ℝ) ≤ (2 : ℝ) ^ ((R : ℝ) / 4) := by
    refine hScard'.trans ?_
    rw [← Real.rpow_natCast (2 : ℝ) (t N A)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) htR
  calc (S.card : ℝ) * ((2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 2))
      ≤ (2 : ℝ) ^ ((R : ℝ) / 4) * ((2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hScardR (by positivity)
    _ = (2 : ℝ) ^ N * (2 : ℝ) ^ (-(R : ℝ) / 4) := by
        have e1 : (2:ℝ) ^ ((R:ℝ)/4) * (2:ℝ) ^ (-(R:ℝ)/2) = (2:ℝ) ^ (-(R:ℝ)/4) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
        rw [show (2:ℝ) ^ ((R:ℝ)/4) * ((2:ℝ) ^ N * (2:ℝ) ^ (-(R:ℝ)/2))
            = (2:ℝ) ^ N * ((2:ℝ) ^ ((R:ℝ)/4) * (2:ℝ) ^ (-(R:ℝ)/2)) from by ring, e1]

open Classical in
/-- `E_A(z)` is bounded by the fraction of bad selectors. -/
theorem Err_le_real (A : AffineSubspace F2 (V N)) (R : ℕ) (z : Fin N → F2) :
    Err N A R z ≤ (Nat.card {σ : Fin N → F2 // R < (U N A σ).card} : ℝ) / 2 ^ N := by
  unfold Err
  gcongr
  have hsum1 : (∑ σ : Fin N → F2, if good N A R σ then (0:ℝ) else condDensity N A σ z)
      ≤ ∑ σ : Fin N → F2, if good N A R σ then (0:ℝ) else 1 := by
    apply Finset.sum_le_sum
    intro σ _
    split_ifs with h
    · exact le_refl 0
    · exact condDensity_le_one N A σ z
  refine hsum1.trans ?_
  have hfilter_eq : (Finset.univ.filter (fun σ : Fin N → F2 => ¬ good N A R σ))
      = (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card)) := by
    apply Finset.filter_congr
    intro σ _
    unfold good
    omega
  have hcard_eq : (Finset.univ.filter (fun σ : Fin N → F2 => R < (U N A σ).card)).card
      = Nat.card {σ : Fin N → F2 // R < (U N A σ).card} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum2 : (∑ σ : Fin N → F2, if good N A R σ then (0:ℝ) else (1:ℝ))
      = ((Finset.univ.filter (fun σ : Fin N → F2 => ¬ good N A R σ)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : good N A R σ <;> simp [h]
  rw [hsum2, hfilter_eq, hcard_eq]

end Lemma53
