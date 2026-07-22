import Revres.SoPL.ApproxNS.Average

/-!
# Row locality for low-degree monomials

Encoded successor and predecessor bits are projected back to their grid rows. A monomial can
therefore touch no more rows than its total degree. Pairing consecutive interior rows then gives a
checked adjacent cut missed by every sufficiently low-degree monomial.
-/

namespace Revres

open Lemma53

namespace SoPL

namespace Encoding

variable {ell : ℕ}

/-- The grid row containing an encoded successor or predecessor bit. -/
def rowOfBit (ell : ℕ)
    (i : Fin (variableCount ell)) : Fin (BinaryPointer.order ell) :=
  ((bitIndexEquiv ell).symm i).1.row

@[simp]
theorem rowOfBit_successorBit (u : Node ell) (b : Fin ell) :
    rowOfBit ell (successorBit ell u b) = u.row := by
  simp [rowOfBit, successorBit]

@[simp]
theorem rowOfBit_predecessorBit (u : Node ell) (b : Fin ell) :
    rowOfBit ell (predecessorBit ell u b) = u.row := by
  simp [rowOfBit, predecessorBit]

end Encoding

namespace ApproxNS

variable {ell k n : ℕ}

/-- The rows containing variables with nonzero exponent in a monomial. -/
def monomialRows (ell : ℕ)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ) :
    Finset (Fin (BinaryPointer.order ell)) :=
  m.support.image (Encoding.rowOfBit ell)

@[simp]
theorem mem_monomialRows_iff
    {m : Fin (Encoding.variableCount ell) →₀ ℕ}
    {r : Fin (BinaryPointer.order ell)} :
    r ∈ monomialRows ell m ↔
      ∃ i ∈ m.support, Encoding.rowOfBit ell i = r := by
  simp [monomialRows]

theorem card_monomialRows_le_support
    (m : Fin (Encoding.variableCount ell) →₀ ℕ) :
    (monomialRows ell m).card ≤ m.support.card := by
  exact Finset.card_image_le

/-- Every supported variable contributes at least one to the full monomial degree. -/
theorem card_support_le_monomialDegree
    (m : Fin (Encoding.variableCount ell) →₀ ℕ) :
    m.support.card ≤ m.sum (fun _ exponent ↦ exponent) := by
  classical
  rw [Finsupp.sum]
  simpa only [Finset.card_eq_sum_ones] using
    (Finset.sum_le_sum fun i hi ↦ Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem card_monomialRows_le_degree
    (m : Fin (Encoding.variableCount ell) →₀ ℕ) :
    (monomialRows ell m).card ≤ m.sum (fun _ exponent ↦ exponent) :=
  (card_monomialRows_le_support m).trans (card_support_le_monomialDegree m)

theorem card_monomialRows_le_totalDegree_of_mem_support
    (p : BooleanPolynomial (Encoding.variableCount ell))
    {m : Fin (Encoding.variableCount ell) →₀ ℕ}
    (hm : m ∈ p.support) :
    (monomialRows ell m).card ≤ p.totalDegree :=
  (card_monomialRows_le_degree m).trans (MvPolynomial.le_totalDegree hm)

theorem card_monomialRows_le_of_mem_support
    (p : BooleanPolynomial (Encoding.variableCount ell))
    {m : Fin (Encoding.variableCount ell) →₀ ℕ}
    (hm : m ∈ p.support) (hdegree : p.totalDegree ≤ k) :
    (monomialRows ell m).card ≤ k :=
  (card_monomialRows_le_totalDegree_of_mem_support p hm).trans hdegree

/-- A cut between two consecutive rows, strictly inside the first and last grid boundaries. -/
structure InteriorCut (n : ℕ) where
  lower : Fin n
  lower_pos : 0 < lower.val
  upper_not_last : lower.val + 2 < n

namespace InteriorCut

/-- The row immediately above an interior cut's lower row. -/
def upper (cut : InteriorCut n) : Fin n :=
  ⟨cut.lower.val + 1, by
    have h := cut.upper_not_last
    omega⟩

@[simp]
theorem upper_val (cut : InteriorCut n) :
    cut.upper.val = cut.lower.val + 1 :=
  rfl

theorem lower_ne_upper (cut : InteriorCut n) : cut.lower ≠ cut.upper := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

theorem lower_ne_zero (cut : InteriorCut n) : cut.lower.val ≠ 0 := by
  have h := cut.lower_pos
  omega

theorem upper_isInternal (cut : InteriorCut n) : cut.upper.val + 1 < n := by
  have h := cut.upper_not_last
  simp only [upper_val]
  omega

end InteriorCut

/-- Fixed room for excluding the first and last rows from the candidate-pair argument. -/
def rowLocalitySlack : ℕ := 4

/-- At most `k` touched rows miss one of `k + 1` disjoint adjacent interior pairs. -/
theorem exists_two_consecutive_rows_untouched
    {n k : ℕ} (rows : Finset (Fin n))
    (hrows : rows.card ≤ k)
    (hsmall : 2 * k + rowLocalitySlack < n) :
    ∃ cut : InteriorCut n,
      cut.lower ∉ rows ∧ cut.upper ∉ rows := by
  classical
  change 2 * k + 4 < n at hsmall
  let candidateCut : Fin (k + 1) → InteriorCut n := fun j ↦
    { lower := ⟨2 * j.val + 1, by
        have hj : j.val ≤ k := by omega
        omega⟩
      lower_pos := by
        change 0 < 2 * j.val + 1
        omega
      upper_not_last := by
        have hj : j.val ≤ k := by omega
        change 2 * j.val + 1 + 2 < n
        omega }
  by_contra hcut
  have hpairs (j : Fin (k + 1)) :
      (candidateCut j).lower ∈ rows ∨ (candidateCut j).upper ∈ rows := by
    by_cases hlower : (candidateCut j).lower ∈ rows
    · exact Or.inl hlower
    by_cases hupper : (candidateCut j).upper ∈ rows
    · exact Or.inr hupper
    exact False.elim (hcut ⟨candidateCut j, hlower, hupper⟩)
  let chosen (j : Fin (k + 1)) : Fin n :=
    if (candidateCut j).lower ∈ rows then
      (candidateCut j).lower
    else
      (candidateCut j).upper
  have chosen_mem (j : Fin (k + 1)) : chosen j ∈ rows := by
    dsimp [chosen]
    split
    · assumption
    · rename_i hlower
      exact (hpairs j).resolve_left hlower
  have chosen_lower_bound (j : Fin (k + 1)) :
      2 * j.val + 1 ≤ (chosen j).val := by
    simp only [chosen]
    split <;> simp [candidateCut, InteriorCut.upper]
  have chosen_upper_bound (j : Fin (k + 1)) :
      (chosen j).val ≤ 2 * j.val + 2 := by
    simp only [chosen]
    split <;> simp [candidateCut, InteriorCut.upper]
  let selected : Fin (k + 1) → ↑rows := fun j ↦ ⟨chosen j, chosen_mem j⟩
  have selected_injective : Function.Injective selected := by
    intro a b hab
    apply Fin.ext
    have hval : (chosen a).val = (chosen b).val :=
      congrArg (fun r : ↑rows ↦ r.1.val) hab
    have halower := chosen_lower_bound a
    have haupper := chosen_upper_bound a
    have hblower := chosen_lower_bound b
    have hbupper := chosen_upper_bound b
    omega
  have hcard := Fintype.card_le_of_injective selected selected_injective
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

theorem exists_monomial_untouched_cut
    {ell k : ℕ}
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (hmdegree : m.sum (fun _ exponent ↦ exponent) ≤ k)
    (hsmall :
      2 * k + rowLocalitySlack < BinaryPointer.order ell) :
    ∃ cut : InteriorCut (BinaryPointer.order ell),
      cut.lower ∉ monomialRows ell m ∧
        cut.upper ∉ monomialRows ell m :=
  exists_two_consecutive_rows_untouched (monomialRows ell m)
    ((card_monomialRows_le_degree m).trans hmdegree) hsmall

theorem exists_support_monomial_untouched_cut
    {ell k : ℕ}
    (p : BooleanPolynomial (Encoding.variableCount ell))
    {m : Fin (Encoding.variableCount ell) →₀ ℕ}
    (hm : m ∈ p.support)
    (hdegree : p.totalDegree ≤ k)
    (hsmall :
      2 * k + rowLocalitySlack < BinaryPointer.order ell) :
    ∃ cut : InteriorCut (BinaryPointer.order ell),
      cut.lower ∉ monomialRows ell m ∧
        cut.upper ∉ monomialRows ell m :=
  exists_two_consecutive_rows_untouched (monomialRows ell m)
    (card_monomialRows_le_of_mem_support p hm hdegree) hsmall

end ApproxNS

end SoPL

end Revres
