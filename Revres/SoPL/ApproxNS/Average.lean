import Revres.SoPL.ApproxNS.ReductionPolynomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite averages for the OR-to-SoPL reduction

The actual experiment averages the planted-sink polynomial over row-permutation seeds. The ideal
experiment averages sink contributions over both seeds and active path labels. All averages are
explicit normalized finite sums.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace SoPL

namespace ApproxNS

/-- The uniform average of a real-valued function on a finite type. -/
noncomputable def finiteAverage {alpha : Type*} [Fintype alpha]
    (f : alpha → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card alpha : ℝ)

theorem finiteAverage_congr {alpha : Type*} [Fintype alpha]
    {f g : alpha → ℝ} (h : ∀ a, f a = g a) :
    finiteAverage f = finiteAverage g := by
  simp only [finiteAverage]
  congr 1
  exact Finset.sum_congr rfl fun a _ha ↦ h a

theorem finiteAverage_bounds {alpha : Type*} [Fintype alpha] [Nonempty alpha]
    {f : alpha → ℝ} {lower upper : ℝ}
    (h : ∀ a, lower ≤ f a ∧ f a ≤ upper) :
    lower ≤ finiteAverage f ∧ finiteAverage f ≤ upper := by
  have hcard : (0 : ℝ) < Fintype.card alpha := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card alpha)
  constructor
  · rw [finiteAverage, le_div_iff₀ hcard]
    calc
      lower * (Fintype.card alpha : ℝ) = ∑ _a : alpha, lower := by
        simp [mul_comm]
      _ ≤ ∑ a : alpha, f a := by
        apply Finset.sum_le_sum
        intro a _ha
        exact (h a).1
  · rw [finiteAverage, div_le_iff₀ hcard]
    calc
      (∑ a : alpha, f a) ≤ ∑ _a : alpha, upper := by
        apply Finset.sum_le_sum
        intro a _ha
        exact (h a).2
      _ = upper * (Fintype.card alpha : ℝ) := by
        simp [mul_comm]

theorem finiteAverage_coe_finset {alpha : Type*}
    (s : Finset alpha) (f : alpha → ℝ) :
    finiteAverage (fun a : ↑s ↦ f a.1) =
      (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [finiteAverage, Fintype.card_coe]
  rw [Finset.sum_coe_sort]

theorem rowPermSeed_card_pos (n : ℕ) :
    0 < Fintype.card (RowPermSeed n) :=
  Fintype.card_pos_iff.mpr ⟨identitySeed n⟩

theorem activeLabels_nonempty {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    (activeLabels hell x).Nonempty :=
  ⟨zeroLabel hell, by simp⟩

theorem activeLabels_card_pos {ell : ℕ} (hell : 0 < ell) (x : ORInput ell) :
    0 < (activeLabels hell x).card :=
  (activeLabels_nonempty hell x).card_pos

variable {ell : ℕ} {hell : 0 < ell}
variable {Qsharp : (Fin (Encoding.variableCount ell) → F2) → ℝ}

/-- The planted-sink contribution after applying one fixed reduction seed. -/
noncomputable def plantedSeedPolynomial
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    BooleanPolynomial (BinaryPointer.order ell - 1) :=
  reductionSubstitution hell seed
    (sinkPolynomial certSharp (plantedSink hell seed))

theorem totalDegree_plantedSeedPolynomial_le
    {degree : ℕ}
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (hdegree : certSharp.DegreeLE degree)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    (plantedSeedPolynomial hell certSharp seed).totalDegree ≤ degree := by
  exact (totalDegree_reductionSubstitution_le hell seed _).trans
    (totalDegree_sinkPolynomial_le_of_degreeLE hdegree (plantedSink hell seed))

/-- The polynomial for the actual planted-sink experiment. -/
noncomputable def actualPolynomial
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp) :
    BooleanPolynomial (BinaryPointer.order ell - 1) :=
  ((Fintype.card (RowPermSeed (BinaryPointer.order ell)) : ℝ)⁻¹) •
    ∑ seed : RowPermSeed (BinaryPointer.order ell),
      plantedSeedPolynomial hell certSharp seed

theorem totalDegree_actualPolynomial_le
    {degree : ℕ}
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (hdegree : certSharp.DegreeLE degree) :
    (actualPolynomial hell certSharp).totalDegree ≤ degree := by
  refine (MvPolynomial.totalDegree_smul_le
    ((Fintype.card (RowPermSeed (BinaryPointer.order ell)) : ℝ)⁻¹) _).trans ?_
  apply MvPolynomial.totalDegree_finsetSum_le
  intro seed _hseed
  exact totalDegree_plantedSeedPolynomial_le certSharp hdegree seed

/-- The pointwise finite average represented by `actualPolynomial`. -/
noncomputable def finiteActualAverage
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) : ℝ :=
  finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
    evalBoolean
      (Encoding.encodeInput ell (reductionInput hell seed x))
      (sinkPolynomial certSharp (plantedSink hell seed))

@[simp]
theorem evalBoolean_actualPolynomial
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    evalBoolean x (actualPolynomial hell certSharp) =
      finiteActualAverage hell certSharp x := by
  simp only [actualPolynomial, finiteActualAverage, finiteAverage,
    Algebra.smul_def, evalBoolean_mul]
  rw [evalBoolean_finset_sum]
  simp_rw [plantedSeedPolynomial, evalBoolean_reductionSubstitution]
  rw [div_eq_mul_inv, mul_comm]
  simp [evalBoolean]

/-- The ideal experiment: choose a seed and then an active path label uniformly. -/
noncomputable def idealValue
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) : ℝ :=
  finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
    finiteAverage fun c : ↑(activeLabels hell x) ↦
      evalBoolean
        (Encoding.encodeInput ell (reductionInput hell seed x))
        (sinkPolynomial certSharp (pathEndpoint hell seed c.1))

/-- The active-label sink sum at a reduced input is the represented certificate value. -/
theorem sum_activeLabel_sink_eq_represented
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (seed : RowPermSeed (BinaryPointer.order ell))
    (x : ORInput ell) :
    (∑ c ∈ activeLabels hell x,
      evalBoolean
        (Encoding.encodeInput ell (reductionInput hell seed x))
        (sinkPolynomial certSharp (pathEndpoint hell seed c))) =
      Qsharp (Encoding.encodeInput ell (reductionInput hell seed x)) := by
  let y := Encoding.encodeInput ell (reductionInput hell seed x)
  symm
  calc
    Qsharp y =
        ∑ u ∈ Encoding.activeLastSet y,
          evalBoolean y (sinkPolynomial certSharp u) :=
      represented_eq_sum_active_sinks certSharp
        (encoded_reduction_isPathFamily hell seed x)
    _ = ∑ u ∈ (activeLabels hell x).image (pathEndpoint hell seed),
          evalBoolean y (sinkPolynomial certSharp u) := by
      rw [activeLastSet_encode_reduction]
    _ = ∑ c ∈ activeLabels hell x,
          evalBoolean y (sinkPolynomial certSharp (pathEndpoint hell seed c)) := by
      rw [Finset.sum_image (pathEndpoint_injective hell seed).injOn]

/-- Rewrite the ideal inner average using the complete certificate combination. -/
theorem idealValue_eq_average_combination_div_card
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    idealValue hell certSharp x =
      finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        evalBoolean
          (Encoding.encodeInput ell (reductionInput hell seed x))
          certSharp.combinationPolynomial /
            ((activeLabels hell x).card : ℝ) := by
  unfold idealValue
  apply finiteAverage_congr
  intro seed
  change finiteAverage
      (fun c : ↑(activeLabels hell x) ↦
        (fun label : Fin (BinaryPointer.order ell) ↦
          evalBoolean
            (Encoding.encodeInput ell (reductionInput hell seed x))
            (sinkPolynomial certSharp (pathEndpoint hell seed label))) c.1) = _
  simp only [finiteAverage, Fintype.card_coe]
  have hsum :
      (∑ c : ↑(activeLabels hell x),
        (fun label : Fin (BinaryPointer.order ell) ↦
          evalBoolean
            (Encoding.encodeInput ell (reductionInput hell seed x))
            (sinkPolynomial certSharp (pathEndpoint hell seed label))) c.1) =
        ∑ c ∈ activeLabels hell x,
          evalBoolean
            (Encoding.encodeInput ell (reductionInput hell seed x))
            (sinkPolynomial certSharp (pathEndpoint hell seed c)) := by
    exact Finset.sum_coe_sort (activeLabels hell x)
      (fun label : Fin (BinaryPointer.order ell) ↦
        evalBoolean
          (Encoding.encodeInput ell (reductionInput hell seed x))
          (sinkPolynomial certSharp (pathEndpoint hell seed label)))
  rw [hsum, sum_activeLabel_sink_eq_represented,
    NSCertificate.evalBoolean_combinationPolynomial]

/-- Rewrite the ideal inner average as the represented value divided by the active-label count. -/
theorem idealValue_eq_average_represented_div_card
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    idealValue hell certSharp x =
      finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        Qsharp (Encoding.encodeInput ell (reductionInput hell seed x)) /
          ((activeLabels hell x).card : ℝ) := by
  rw [idealValue_eq_average_combination_div_card]
  apply finiteAverage_congr
  intro seed
  rw [NSCertificate.evalBoolean_combinationPolynomial]

theorem idealValue_eq_average_represented_div_hammingWeight
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    idealValue hell certSharp x =
      finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        Qsharp (Encoding.encodeInput ell (reductionInput hell seed x)) /
          ((1 + hammingWeight x : ℕ) : ℝ) := by
  rw [idealValue_eq_average_represented_div_card]
  apply finiteAverage_congr
  intro seed
  rw [activeLabels_card]

theorem idealValue_bounds_of_hammingWeight_eq_zero
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (hsharp : ∀ y, IsEncodedPathFamily ell hell y →
      (255 / 256 : ℝ) ≤ Qsharp y ∧ Qsharp y ≤ 1)
    (x : ORInput ell) (hzero : hammingWeight x = 0) :
    (255 / 256 : ℝ) ≤ idealValue hell certSharp x ∧
      idealValue hell certSharp x ≤ 1 := by
  letI : Nonempty (RowPermSeed (BinaryPointer.order ell)) :=
    ⟨identitySeed (BinaryPointer.order ell)⟩
  rw [idealValue_eq_average_represented_div_hammingWeight]
  apply finiteAverage_bounds
  intro seed
  simpa [hzero] using
    hsharp _ (encoded_reduction_isPathFamily hell seed x)

theorem idealValue_bounds_of_hammingWeight_pos
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (hsharp : ∀ y, IsEncodedPathFamily ell hell y →
      (255 / 256 : ℝ) ≤ Qsharp y ∧ Qsharp y ≤ 1)
    (x : ORInput ell) (hpos : 0 < hammingWeight x) :
    0 ≤ idealValue hell certSharp x ∧
      idealValue hell certSharp x ≤ (1 / 2 : ℝ) := by
  letI : Nonempty (RowPermSeed (BinaryPointer.order ell)) :=
    ⟨identitySeed (BinaryPointer.order ell)⟩
  rw [idealValue_eq_average_represented_div_hammingWeight]
  apply finiteAverage_bounds
  intro seed
  let y := Encoding.encodeInput ell (reductionInput hell seed x)
  have hQ := hsharp y (encoded_reduction_isPathFamily hell seed x)
  have hdenNat : 2 ≤ 1 + hammingWeight x := by omega
  have hden : (2 : ℝ) ≤ ((1 + hammingWeight x : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hdenPos : (0 : ℝ) < ((1 + hammingWeight x : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) hden
  constructor
  · exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 255 / 256).trans hQ.1)
      hdenPos.le
  · apply (div_le_iff₀ hdenPos).2
    linarith

end ApproxNS

end SoPL

end Revres
