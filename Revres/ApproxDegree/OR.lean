import Revres.ApproxDegree.DiscreteMarkov

/-!
# An explicit approximate-degree lower bound for OR

The finite symmetrization polynomial is rescaled to meet the hypotheses of the discrete Markov
inequality. This gives a quadratic bound with the same explicit constant.
-/

namespace Revres

open Lemma53

namespace ApproxDegree

/-- The explicit constant in the finite approximate-degree bound for OR. -/
def C_or : ℕ := C_markov

/-- Every real polynomial that `1/3`-approximates OR on the Boolean cube has quadratically
bounded dimension in its total degree. -/
theorem or_approx_degree_quadratic {m : ℕ} (p : BooleanPolynomial m)
    (happrox : ∀ x : Fin m → F2,
      |evalBoolean x p - orValue x| ≤ (1 / 3 : ℝ)) :
    m ≤ C_or * (p.totalDegree + 1) ^ 2 := by
  by_cases hmzero : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
    have hmOne : 1 ≤ m := hmpos
    obtain ⟨q, hqDegree, hqZero, hqPositive⟩ :=
      exists_univariate_of_or_approximator
        (d := p.totalDegree) p le_rfl happrox
    let r : Polynomial ℝ := (3 / 4 : ℝ) • q
    have hrDegree : r.natDegree ≤ p.totalDegree := by
      exact (Polynomial.natDegree_smul_le (3 / 4 : ℝ) q).trans hqDegree
    have hrGrid : ∀ j : ℕ, j ≤ m → |r.eval (j : ℝ)| ≤ 1 := by
      intro j hjm
      by_cases hjzero : j = 0
      · subst j
        simp only [Nat.cast_zero]
        rw [show r.eval (0 : ℝ) = (3 / 4 : ℝ) * q.eval 0 by simp [r], abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
        nlinarith
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
        have hqj := hqPositive j hjpos hjm
        have hqjAbs : |q.eval (j : ℝ)| ≤ (4 / 3 : ℝ) := by
          calc
            |q.eval (j : ℝ)| = |(q.eval (j : ℝ) - 1) + 1| := by
              congr 1
              ring
            _ ≤ |q.eval (j : ℝ) - 1| + |(1 : ℝ)| :=
              abs_add_le (q.eval (j : ℝ) - 1) 1
            _ ≤ (4 / 3 : ℝ) := by
              norm_num at hqj ⊢
              linarith
        rw [show r.eval (j : ℝ) = (3 / 4 : ℝ) * q.eval (j : ℝ) by simp [r],
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
        nlinarith
    have hqOne := hqPositive 1 (by norm_num) hmOne
    have hqOneError : |1 - q.eval 1| ≤ (1 / 3 : ℝ) := by
      rw [abs_sub_comm]
      simpa using hqOne
    have hqJump : (1 / 3 : ℝ) ≤ |q.eval 1 - q.eval 0| := by
      have hfirst := abs_add_le (1 - q.eval 1) (q.eval 1 - q.eval 0)
      have hsum :
          (1 - q.eval 1) + (q.eval 1 - q.eval 0) + q.eval 0 = (1 : ℝ) := by
        ring
      have hsecond := abs_add_le
        ((1 - q.eval 1) + (q.eval 1 - q.eval 0)) (q.eval 0)
      rw [hsum, abs_one] at hsecond
      nlinarith
    have hrJump : (1 / 4 : ℝ) ≤ |r.eval 1 - r.eval 0| := by
      rw [show r.eval 1 - r.eval 0 =
        (3 / 4 : ℝ) * (q.eval 1 - q.eval 0) by simp [r]; ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      nlinarith
    have hbound := integer_grid_jump_degree_bound r hrDegree hrGrid hrJump
    simpa [C_or] using hbound

end ApproxDegree

end Revres
