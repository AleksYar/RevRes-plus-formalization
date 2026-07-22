import Revres.ApproxDegree.Symmetrize
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A discrete Markov inequality on the integer grid

This file derives one explicit sampled-polynomial estimate.  It uses the Chebyshev extremal
theorem at an endpoint, affine rescaling, and a compactness bootstrap from integer samples.
-/

namespace Revres

namespace ApproxDegree

open Set
open Polynomial

/-- The endpoint derivative form of Markov's inequality on `[-1, 1]`. -/
theorem abs_derivative_eval_one_le_sq {n : ℕ} {p : Polynomial ℝ}
    (hdeg : p.natDegree ≤ n)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 := by
  have hdegree : p.degree ≤ (n : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le hdeg
  have hupper :=
    Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := n) (P := p) (k := 1) (x := 1) (by norm_num) hdegree hbound
  have hnegDegree : (-p).degree ≤ (n : WithBot ℕ) := by
    simpa using hdegree
  have hnegBound : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |(-p).eval x| ≤ 1 := by
    intro x hx
    simpa using hbound x hx
  have hlower :=
    Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := n) (P := -p) (k := 1) (x := 1) (by norm_num) hnegDegree hnegBound
  simp only [Function.iterate_one, Polynomial.derivative_neg, Polynomial.eval_neg] at hupper hlower
  rw [Polynomial.Chebyshev.derivative_T_eval_one] at hupper hlower
  have hupper' : p.derivative.eval 1 ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hupper
  have hlower' : -(n : ℝ) ^ 2 ≤ p.derivative.eval 1 := by
    have : -p.derivative.eval 1 ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast hlower
    linarith
  exact abs_le.mpr ⟨hlower', hupper'⟩

/-- The affine polynomial `a X + b`. -/
noncomputable def affinePolynomial (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

@[simp]
theorem eval_affinePolynomial (a b x : ℝ) :
    (affinePolynomial a b).eval x = a * x + b := by
  simp [affinePolynomial]

theorem natDegree_affinePolynomial_le (a b : ℝ) :
    (affinePolynomial a b).natDegree ≤ 1 := by
  exact Polynomial.natDegree_linear_le

@[simp]
theorem derivative_affinePolynomial (a b : ℝ) :
    (affinePolynomial a b).derivative = Polynomial.C a := by
  simp [affinePolynomial]

theorem natDegree_comp_affinePolynomial_le {n : ℕ} (p : Polynomial ℝ)
    (hdeg : p.natDegree ≤ n) (a b : ℝ) :
    (p.comp (affinePolynomial a b)).natDegree ≤ n := by
  calc
    (p.comp (affinePolynomial a b)).natDegree ≤
        p.natDegree * (affinePolynomial a b).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ n * 1 := Nat.mul_le_mul hdeg (natDegree_affinePolynomial_le a b)
    _ = n := Nat.mul_one n

@[simp]
theorem derivative_comp_affinePolynomial_eval (p : Polynomial ℝ) (a b x : ℝ) :
    (p.comp (affinePolynomial a b)).derivative.eval x =
      a * p.derivative.eval (a * x + b) := by
  rw [Polynomial.derivative_comp]
  simp

/-- A factor-two pointwise Markov bound on `[-1, 1]`.

The loss of two lets us map the longer of `[-1,x]` and `[x,1]` to the unit interval and use only
the endpoint extremal theorem. -/
theorem abs_derivative_eval_le_two_sq {n : ℕ} {p : Polynomial ℝ}
    (hdeg : p.natDegree ≤ n)
    (hbound : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |p.eval y| ≤ 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |p.derivative.eval x| ≤ 2 * (n : ℝ) ^ 2 := by
  rcases hx with ⟨hxLower, hxUpper⟩
  by_cases hxNonneg : 0 ≤ x
  · let a : ℝ := (x + 1) / 2
    let b : ℝ := (x - 1) / 2
    let r := p.comp (affinePolynomial a b)
    have haNonneg : 0 ≤ a := by
      dsimp [a]
      linarith
    have haHalf : (1 / 2 : ℝ) ≤ a := by
      dsimp [a]
      linarith
    have hrBound : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |r.eval y| ≤ 1 := by
      intro y hy
      rw [show r.eval y = p.eval (a * y + b) by simp [r]]
      apply hbound
      change -1 ≤ a * y + b ∧ a * y + b ≤ 1
      rcases hy with ⟨hyLower, hyUpper⟩
      constructor
      · dsimp [a, b]
        nlinarith
      · dsimp [a, b]
        nlinarith
    have hrDegree : r.natDegree ≤ n :=
      natDegree_comp_affinePolynomial_le p hdeg a b
    have hrMarkov := abs_derivative_eval_one_le_sq hrDegree hrBound
    have heval : a + b = x := by
      dsimp [a, b]
      ring
    rw [show r.derivative.eval 1 = a * p.derivative.eval (a + b) by simp [r],
      heval] at hrMarkov
    rw [abs_mul, abs_of_nonneg haNonneg] at hrMarkov
    have habs : 0 ≤ |p.derivative.eval x| := abs_nonneg _
    nlinarith [sq_nonneg (n : ℝ)]
  · have hxNonpos : x ≤ 0 := le_of_not_ge hxNonneg
    let a : ℝ := (x - 1) / 2
    let b : ℝ := (x + 1) / 2
    let r := p.comp (affinePolynomial a b)
    have haNonpos : a ≤ 0 := by
      dsimp [a]
      linarith
    have haAbsHalf : (1 / 2 : ℝ) ≤ |a| := by
      rw [abs_of_nonpos haNonpos]
      dsimp [a]
      linarith
    have hrBound : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |r.eval y| ≤ 1 := by
      intro y hy
      rw [show r.eval y = p.eval (a * y + b) by simp [r]]
      apply hbound
      change -1 ≤ a * y + b ∧ a * y + b ≤ 1
      rcases hy with ⟨hyLower, hyUpper⟩
      constructor
      · dsimp [a, b]
        nlinarith
      · dsimp [a, b]
        nlinarith
    have hrDegree : r.natDegree ≤ n :=
      natDegree_comp_affinePolynomial_le p hdeg a b
    have hrMarkov := abs_derivative_eval_one_le_sq hrDegree hrBound
    have heval : a + b = x := by
      dsimp [a, b]
      ring
    rw [show r.derivative.eval 1 = a * p.derivative.eval (a + b) by simp [r],
      heval] at hrMarkov
    rw [abs_mul] at hrMarkov
    have habs : 0 ≤ |p.derivative.eval x| := abs_nonneg _
    nlinarith [sq_nonneg (n : ℝ)]

/-- The factor-four derivative bound after scaling `[0,m]` to `[-1,1]`. -/
theorem abs_derivative_eval_interval_le {m n : ℕ} {p : Polynomial ℝ}
    {M x : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hdeg : p.natDegree ≤ n)
    (hbound : ∀ y : ℝ, y ∈ Set.Icc 0 (m : ℝ) → |p.eval y| ≤ M)
    (hx : x ∈ Set.Icc 0 (m : ℝ)) :
    |p.derivative.eval x| ≤
      (4 * (n : ℝ) ^ 2 * M) / (m : ℝ) := by
  let mR : ℝ := m
  let a : ℝ := mR / 2
  let scaled : Polynomial ℝ := M⁻¹ • p
  let r : Polynomial ℝ := scaled.comp (affinePolynomial a a)
  let t : ℝ := 2 * x / mR - 1
  have hmR : 0 < mR := by
    dsimp [mR]
    exact_mod_cast hm
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM
  have ht : t ∈ Set.Icc (-1) 1 := by
    rcases hx with ⟨hxLower, hxUpper⟩
    constructor
    · dsimp [t]
      have : 0 ≤ 2 * x / mR := div_nonneg (mul_nonneg (by norm_num) hxLower) hmR.le
      linarith
    · dsimp [t]
      apply sub_le_iff_le_add.mpr
      rw [show (1 : ℝ) + 1 = 2 by norm_num]
      apply (div_le_iff₀ hmR).2
      dsimp [mR] at hxUpper ⊢
      nlinarith
  have hat : a * t + a = x := by
    dsimp [a, t]
    field_simp
    ring
  have hrBound : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |r.eval y| ≤ 1 := by
    intro y hy
    have hz : a * y + a ∈ Set.Icc 0 (m : ℝ) := by
      rcases hy with ⟨hyLower, hyUpper⟩
      constructor
      · dsimp [a, mR]
        nlinarith
      · dsimp [a, mR]
        nlinarith
    have hpBound := hbound (a * y + a) hz
    rw [show r.eval y = M⁻¹ * p.eval (a * y + a) by simp [r, scaled]]
    rw [abs_mul, abs_of_pos hMinv]
    calc
      M⁻¹ * |p.eval (a * y + a)| ≤ M⁻¹ * M :=
        mul_le_mul_of_nonneg_left hpBound hMinv.le
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hscaledDegree : scaled.natDegree ≤ n := by
    exact (Polynomial.natDegree_smul_le M⁻¹ p).trans hdeg
  have hrDegree : r.natDegree ≤ n :=
    natDegree_comp_affinePolynomial_le scaled hscaledDegree a a
  have hrMarkov := abs_derivative_eval_le_two_sq hrDegree hrBound ht
  have hrDerivative :
      r.derivative.eval t = a * (M⁻¹ * p.derivative.eval x) := by
    rw [show r.derivative.eval t =
      a * scaled.derivative.eval (a * t + a) by simp [r]]
    rw [hat]
    simp [scaled]
  rw [hrDerivative, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hMinv] at hrMarkov
  have hhalf :
      ((m : ℝ) / 2) * |p.derivative.eval x| ≤
        2 * (n : ℝ) ^ 2 * M := by
    calc
      ((m : ℝ) / 2) * |p.derivative.eval x| =
          M * (a * (M⁻¹ * |p.derivative.eval x|)) := by
        dsimp [a, mR]
        field_simp
      _ ≤ M * (2 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hrMarkov hM.le
      _ = 2 * (n : ℝ) ^ 2 * M := by ring
  apply (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))).2
  nlinarith

/-- The absolute value of a polynomial attains a maximum on a closed interval. -/
theorem exists_abs_eval_max_Icc (p : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ x : ℝ, x ∈ Set.Icc a b ∧
      ∀ y : ℝ, y ∈ Set.Icc a b → |p.eval y| ≤ |p.eval x| := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab)
    (show ContinuousOn (fun y : ℝ ↦ |p.eval y|) (Set.Icc a b) from
      p.differentiable.continuous.abs.continuousOn)
  exact ⟨x, hx, hmax⟩

/-- Mean-value control for polynomial evaluation from a bound on its formal derivative. -/
theorem abs_eval_sub_eval_le_of_derivative_bound {p : Polynomial ℝ}
    {a b C x y : ℝ}
    (hderiv : ∀ z : ℝ, z ∈ Set.Icc a b → |p.derivative.eval z| ≤ C)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |p.eval y - p.eval x| ≤ C * |y - x| := by
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z : ℝ ↦ p.eval z) (f' := fun z : ℝ ↦ p.derivative.eval z)
      (s := Set.Icc a b) (C := C)
      (fun z _ ↦ (p.hasDerivAt z).hasDerivWithinAt)
      (by simpa [Real.norm_eq_abs] using hderiv)
      (convex_Icc a b) hx hy)

/-- Integer-grid boundedness controls the polynomial on the whole interval once the grid is
long compared with the square of the degree budget. -/
theorem abs_eval_le_two_of_integer_grid {m d : ℕ} (q : Polynomial ℝ)
    (hlarge : 8 * (d + 1) ^ 2 ≤ m)
    (hdeg : q.natDegree ≤ d)
    (hgrid : ∀ j : ℕ, j ≤ m → |q.eval (j : ℝ)| ≤ 1)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (m : ℝ)) :
    |q.eval x| ≤ 2 := by
  have hpositive : 0 < 8 * (d + 1) ^ 2 := by positivity
  have hm : 0 < m := hpositive.trans_le hlarge
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨xMax, hxMax, hmax⟩ :=
    exists_abs_eval_max_Icc q (show (0 : ℝ) ≤ (m : ℝ) by positivity)
  let M : ℝ := |q.eval xMax|
  by_cases hMzero : M = 0
  · calc
      |q.eval x| ≤ M := hmax x hx
      _ ≤ 2 := by simp [hMzero]
  · have hMpos : 0 < M :=
      lt_of_le_of_ne (by exact abs_nonneg (q.eval xMax)) (Ne.symm hMzero)
    have hdegree : q.natDegree ≤ d + 1 := hdeg.trans (by omega)
    have hderiv : ∀ z : ℝ, z ∈ Set.Icc 0 (m : ℝ) →
        |q.derivative.eval z| ≤
          (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ) := by
      intro z hz
      exact abs_derivative_eval_interval_le hm hMpos hdegree
        (fun y hy ↦ hmax y hy) hz
    let j : ℕ := ⌊xMax⌋₊
    have hjm : j ≤ m := by
      dsimp [j]
      exact Nat.floor_le_of_le hxMax.2
    have hjmem : (j : ℝ) ∈ Set.Icc 0 (m : ℝ) := by
      constructor
      · positivity
      · exact_mod_cast hjm
    have hdist : |xMax - (j : ℝ)| ≤ 1 := by
      simpa [j] using (Nat.abs_sub_floor_le hxMax.1)
    have hdiff : |q.eval xMax - q.eval (j : ℝ)| ≤
        (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ) := by
      have hmv := abs_eval_sub_eval_le_of_derivative_bound hderiv hjmem hxMax
      calc
        |q.eval xMax - q.eval (j : ℝ)| ≤
            ((4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ)) *
              |xMax - (j : ℝ)| := hmv
        _ ≤ ((4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ)) * 1 := by
          apply mul_le_mul_of_nonneg_left hdist
          positivity
        _ = (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ) := by ring
    have htriangle : M ≤ |q.eval (j : ℝ)| +
        |q.eval xMax - q.eval (j : ℝ)| := by
      dsimp [M]
      calc
        |q.eval xMax| =
            |q.eval (j : ℝ) + (q.eval xMax - q.eval (j : ℝ))| := by
          congr 1
          ring
        _ ≤ |q.eval (j : ℝ)| + |q.eval xMax - q.eval (j : ℝ)| :=
          abs_add_le (q.eval (j : ℝ)) (q.eval xMax - q.eval (j : ℝ))
    have hMineq : M ≤ 1 +
        (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ) :=
      htriangle.trans (add_le_add (hgrid j hjm) hdiff)
    have hlargeR :
        (8 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by
      exact_mod_cast hlarge
    have hcoef :
        (4 * ((d + 1 : ℕ) : ℝ) ^ 2) / (m : ℝ) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hmR).2
      nlinarith
    have hrewrite :
        (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * M) / (m : ℝ) =
          ((4 * ((d + 1 : ℕ) : ℝ) ^ 2) / (m : ℝ)) * M := by
      field_simp
    rw [hrewrite] at hMineq
    have hscaled := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (q.eval xMax))
    have hMle : M ≤ 2 := by
      nlinarith
    exact (hmax x hx).trans hMle

/-- The explicit constant in the integer-grid jump bound. -/
def C_markov : ℕ := 32

/-- A polynomial bounded on `0, ..., m` and making a fixed jump from zero to one has
quadratically bounded grid length. -/
theorem integer_grid_jump_degree_bound {m d : ℕ} (q : Polynomial ℝ)
    (hdeg : q.natDegree ≤ d)
    (hgrid : ∀ j : ℕ, j ≤ m → |q.eval (j : ℝ)| ≤ 1)
    (hjump : (1 / 4 : ℝ) ≤ |q.eval 1 - q.eval 0|) :
    m ≤ C_markov * (d + 1) ^ 2 := by
  by_cases hlarge : 8 * (d + 1) ^ 2 ≤ m
  · have hpositive : 0 < 8 * (d + 1) ^ 2 := by positivity
    have hm : 0 < m := hpositive.trans_le hlarge
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdegree : q.natDegree ≤ d + 1 := hdeg.trans (by omega)
    have hcontinuous : ∀ x : ℝ, x ∈ Set.Icc 0 (m : ℝ) → |q.eval x| ≤ 2 := by
      intro x hx
      exact abs_eval_le_two_of_integer_grid q hlarge hdeg hgrid hx
    have hderiv : ∀ x : ℝ, x ∈ Set.Icc 0 (m : ℝ) →
        |q.derivative.eval x| ≤
          (8 * ((d + 1 : ℕ) : ℝ) ^ 2) / (m : ℝ) := by
      intro x hx
      convert abs_derivative_eval_interval_le hm (by norm_num : (0 : ℝ) < 2)
        hdegree hcontinuous hx using 1
      ring
    have hmOne : 1 ≤ m := by omega
    have hzero : (0 : ℝ) ∈ Set.Icc 0 (m : ℝ) := by
      constructor <;> positivity
    have hone : (1 : ℝ) ∈ Set.Icc 0 (m : ℝ) := by
      constructor
      · norm_num
      · exact_mod_cast hmOne
    have hmv := abs_eval_sub_eval_le_of_derivative_bound hderiv hzero hone
    have hjumpUpper : |q.eval 1 - q.eval 0| ≤
        (8 * ((d + 1 : ℕ) : ℝ) ^ 2) / (m : ℝ) := by
      simpa using hmv
    have hratio : (1 / 4 : ℝ) ≤
        (8 * ((d + 1 : ℕ) : ℝ) ^ 2) / (m : ℝ) :=
      hjump.trans hjumpUpper
    have hproduct := (le_div_iff₀ hmR).mp hratio
    have hreal : (m : ℝ) ≤ 32 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    unfold C_markov
    exact_mod_cast hreal
  · unfold C_markov
    omega

end ApproxDegree

end Revres
