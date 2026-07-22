import Revres.SoPL.ApproxNS.Reroute

/-!
# Monomial-level local indistinguishability

For a fixed physical sink and monomial, one untouched cut reindexes planted-endpoint seeds into
selected-endpoint seeds. The monomial is unchanged because rerouting modifies encoded bits only on
the two unread cut rows. Expanding each sink polynomial then identifies the actual and ideal finite
experiments.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace SoPL

namespace ApproxNS

theorem finiteAverage_const {alpha : Type*} [Fintype alpha] [Nonempty alpha]
    (r : ℝ) :
    finiteAverage (fun _ : alpha ↦ r) = r := by
  rw [finiteAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem finiteAverage_add {alpha : Type*} [Fintype alpha]
    (f g : alpha → ℝ) :
    finiteAverage (fun a ↦ f a + g a) = finiteAverage f + finiteAverage g := by
  simp [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_const_mul {alpha : Type*} [Fintype alpha]
    (r : ℝ) (f : alpha → ℝ) :
    finiteAverage (fun a ↦ r * f a) = r * finiteAverage f := by
  simp only [finiteAverage, ← Finset.mul_sum]
  ring

theorem finiteAverage_finset_sum {alpha beta : Type*} [Fintype alpha]
    (s : Finset beta) (f : beta → alpha → ℝ) :
    finiteAverage (fun a ↦ ∑ b ∈ s, f b a) =
      ∑ b ∈ s, finiteAverage (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteAverage]
  | @insert b s hb ih =>
      simp only [Finset.sum_insert hb]
      rw [finiteAverage_add, ih]

theorem finiteAverage_fintype_sum {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] (f : beta → alpha → ℝ) :
    finiteAverage (fun a ↦ ∑ b, f b a) = ∑ b, finiteAverage (f b) := by
  simpa using finiteAverage_finset_sum (Finset.univ : Finset beta) f

theorem finiteAverage_equiv {alpha beta : Type*}
    [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (f : beta → ℝ) :
    finiteAverage (fun a ↦ f (e a)) = finiteAverage f := by
  rw [finiteAverage, finiteAverage, e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_comm {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] (f : alpha → beta → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (f a)) =
      finiteAverage (fun b ↦ finiteAverage (fun a ↦ f a b)) := by
  simp only [finiteAverage, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem finiteAverage₂_const_mul {alpha beta : Type*}
    [Fintype alpha] [Fintype beta]
    (r : ℝ) (f : alpha → beta → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ r * f a b)) =
      r * finiteAverage (fun a ↦ finiteAverage (f a)) := by
  calc
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ r * f a b)) =
        finiteAverage (fun a ↦ r * finiteAverage (f a)) := by
      apply finiteAverage_congr
      intro a
      exact finiteAverage_const_mul r (f a)
    _ = r * finiteAverage (fun a ↦ finiteAverage (f a)) :=
      finiteAverage_const_mul r _

theorem finiteAverage₂_finset_sum {alpha beta gamma : Type*}
    [Fintype alpha] [Fintype beta]
    (s : Finset gamma) (f : gamma → alpha → beta → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ ∑ c ∈ s, f c a b)) =
      ∑ c ∈ s, finiteAverage (fun a ↦ finiteAverage (f c a)) := by
  calc
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ ∑ c ∈ s, f c a b)) =
        finiteAverage (fun a ↦ ∑ c ∈ s, finiteAverage (f c a)) := by
      apply finiteAverage_congr
      intro a
      exact finiteAverage_finset_sum s (fun c b ↦ f c a b)
    _ = ∑ c ∈ s, finiteAverage (fun a ↦ finiteAverage (f c a)) :=
      finiteAverage_finset_sum s _

theorem finiteAverage₂_fintype_sum {alpha beta gamma : Type*}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (f : gamma → alpha → beta → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ ∑ c, f c a b)) =
      ∑ c, finiteAverage (fun a ↦ finiteAverage (f c a)) := by
  simpa using finiteAverage₂_finset_sum (Finset.univ : Finset gamma) f

variable {ell k : ℕ} {x : ORInput ell}

/-- Evaluation of a unit-coefficient monomial on a Boolean assignment. -/
noncomputable def monomialValue
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (y : Fin (Encoding.variableCount ell) → F2) : ℝ :=
  m.prod fun i exponent ↦ f2ToReal (y i) ^ exponent

theorem evalBoolean_monomial
    (m : Fin (Encoding.variableCount ell) →₀ ℕ) (r : ℝ)
    (y : Fin (Encoding.variableCount ell) → F2) :
    evalBoolean y (MvPolynomial.monomial m r) = r * monomialValue m y := by
  simp [evalBoolean, monomialValue, MvPolynomial.eval_monomial]

theorem evalBoolean_eq_sum_monomialValue
    (p : BooleanPolynomial (Encoding.variableCount ell))
    (y : Fin (Encoding.variableCount ell) → F2) :
    evalBoolean y p =
      ∑ m ∈ p.support, p.coeff m * monomialValue m y := by
  calc
    evalBoolean y p =
        evalBoolean y
          (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
      exact congrArg (evalBoolean y) (MvPolynomial.as_sum p)
    _ = ∑ m ∈ p.support,
          evalBoolean y (MvPolynomial.monomial m (p.coeff m)) := by
      rw [evalBoolean_finset_sum]
    _ = ∑ m ∈ p.support, p.coeff m * monomialValue m y := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact evalBoolean_monomial m (p.coeff m) y

theorem monomialValue_congr
    {m : Fin (Encoding.variableCount ell) →₀ ℕ}
    {y z : Fin (Encoding.variableCount ell) → F2}
    (h : ∀ i ∈ m.support, y i = z i) :
    monomialValue m y = monomialValue m z := by
  classical
  unfold monomialValue Finsupp.prod
  apply Finset.prod_congr rfl
  intro i hi
  change f2ToReal (y i) ^ m i = f2ToReal (z i) ^ m i
  rw [h i hi]

theorem monomialValue_reroute_eq
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (seed : RowPermSeed (BinaryPointer.order ell))
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (hlower : cut.lower ∉ monomialRows ell m)
    (hupper : cut.upper ∉ monomialRows ell m) :
    monomialValue m
        (reductionAssignment hell (rerouteSeed hell cut a seed) x) =
      monomialValue m (reductionAssignment hell seed x) := by
  apply monomialValue_congr
  intro i hi
  by_contra hchange
  rcases reroute_changed_bit_rows hell cut a seed i hchange with hrow | hrow
  · exact hlower ((mem_monomialRows_iff).2 ⟨i, hi, hrow⟩)
  · exact hupper ((mem_monomialRows_iff).2 ⟨i, hi, hrow⟩)

/-- Seeds whose planted path has physical endpoint `u`. -/
noncomputable def plantedSeedFiber (hell : 0 < ell) (u : Encoding.Node ell) :
    Finset (RowPermSeed (BinaryPointer.order ell)) := by
  classical
  exact Finset.univ.filter fun seed ↦ plantedSink hell seed = u

@[simp]
theorem mem_plantedSeedFiber
    (hell : 0 < ell) (u : Encoding.Node ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    seed ∈ plantedSeedFiber hell u ↔ plantedSink hell seed = u := by
  classical
  simp [plantedSeedFiber]

/-- Seeds whose path with selected label `a` has physical endpoint `u`. -/
noncomputable def selectedSeedFiber
    (hell : 0 < ell) (x : ORInput ell)
    (a : ↑(activeLabels hell x)) (u : Encoding.Node ell) :
    Finset (RowPermSeed (BinaryPointer.order ell)) := by
  classical
  exact Finset.univ.filter fun seed ↦ pathEndpoint hell seed a.1 = u

@[simp]
theorem mem_selectedSeedFiber
    (hell : 0 < ell) (x : ORInput ell)
    (a : ↑(activeLabels hell x)) (u : Encoding.Node ell)
    (seed : RowPermSeed (BinaryPointer.order ell)) :
    seed ∈ selectedSeedFiber hell x a u ↔ pathEndpoint hell seed a.1 = u := by
  classical
  simp [selectedSeedFiber]

/-- Rerouting restricts to the corresponding fixed-physical-endpoint seed fibers. -/
noncomputable def rerouteSeedFiberEquiv
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (u : Encoding.Node ell) :
    ↑(plantedSeedFiber hell u) ≃ ↑(selectedSeedFiber hell x a u) where
  toFun seed := ⟨rerouteSeed hell cut a seed.1, by
    rw [mem_selectedSeedFiber,
      ← planted_endpoint_becomes_selected_endpoint hell cut a seed.1]
    exact (mem_plantedSeedFiber hell u seed.1).mp seed.2⟩
  invFun seed := ⟨rerouteSeed hell cut a seed.1, by
    rw [mem_plantedSeedFiber,
      rerouted_planted_endpoint_eq_selected_endpoint hell cut a seed.1]
    exact (mem_selectedSeedFiber hell x a u seed.1).mp seed.2⟩
  left_inv seed := by
    apply Subtype.ext
    exact rerouteSeed_involutive hell cut a seed.1
  right_inv seed := by
    apply Subtype.ext
    exact rerouteSeed_involutive hell cut a seed.1

@[simp]
theorem rerouteSeedFiberEquiv_val
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (u : Encoding.Node ell)
    (seed : ↑(plantedSeedFiber hell u)) :
    (rerouteSeedFiberEquiv hell cut a u seed).1 =
      rerouteSeed hell cut a seed.1 :=
  rfl

/-- The planted-endpoint contribution of one monomial, with the global seed normalization. -/
noncomputable def actualMonomialAverage
    (hell : 0 < ell) (u : Encoding.Node ell)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (x : ORInput ell) : ℝ :=
  finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
    if plantedSink hell seed = u then
      monomialValue m (reductionAssignment hell seed x)
    else 0

/-- The selected-endpoint contribution of one monomial, with both global normalizations. -/
noncomputable def idealMonomialAverage
    (hell : 0 < ell) (u : Encoding.Node ell)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (x : ORInput ell) : ℝ :=
  finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
    finiteAverage fun a : ↑(activeLabels hell x) ↦
      if pathEndpoint hell seed a.1 = u then
        monomialValue m (reductionAssignment hell seed x)
      else 0

theorem sum_ite_planted_eq_sum_fiber
    (hell : 0 < ell) (u : Encoding.Node ell)
    (f : RowPermSeed (BinaryPointer.order ell) → ℝ) :
    (∑ seed : RowPermSeed (BinaryPointer.order ell),
      if plantedSink hell seed = u then f seed else 0) =
      ∑ seed : ↑(plantedSeedFiber hell u), f seed.1 := by
  classical
  rw [Finset.sum_coe_sort]
  simp [plantedSeedFiber, Finset.sum_filter]

theorem sum_ite_selected_eq_sum_fiber
    (hell : 0 < ell) (x : ORInput ell)
    (a : ↑(activeLabels hell x)) (u : Encoding.Node ell)
    (f : RowPermSeed (BinaryPointer.order ell) → ℝ) :
    (∑ seed : RowPermSeed (BinaryPointer.order ell),
      if pathEndpoint hell seed a.1 = u then f seed else 0) =
      ∑ seed : ↑(selectedSeedFiber hell x a u), f seed.1 := by
  classical
  rw [Finset.sum_coe_sort]
  simp [selectedSeedFiber, Finset.sum_filter]

theorem planted_monomial_fiber_sum_eq_selected
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (u : Encoding.Node ell)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (hlower : cut.lower ∉ monomialRows ell m)
    (hupper : cut.upper ∉ monomialRows ell m) :
    (∑ seed : ↑(plantedSeedFiber hell u),
      monomialValue m (reductionAssignment hell seed.1 x)) =
      ∑ seed : ↑(selectedSeedFiber hell x a u),
        monomialValue m (reductionAssignment hell seed.1 x) := by
  apply Fintype.sum_equiv (rerouteSeedFiberEquiv hell cut a u)
  intro seed
  exact (monomialValue_reroute_eq hell cut a seed.1 m hlower hupper).symm

theorem actualMonomialAverage_eq_selectedAverage
    (hell : 0 < ell)
    (cut : InteriorCut (BinaryPointer.order ell))
    (a : ↑(activeLabels hell x))
    (u : Encoding.Node ell)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (hlower : cut.lower ∉ monomialRows ell m)
    (hupper : cut.upper ∉ monomialRows ell m) :
    actualMonomialAverage hell u m x =
      finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        if pathEndpoint hell seed a.1 = u then
          monomialValue m (reductionAssignment hell seed x)
        else 0 := by
  unfold actualMonomialAverage finiteAverage
  congr 1
  rw [sum_ite_planted_eq_sum_fiber, sum_ite_selected_eq_sum_fiber]
  exact planted_monomial_fiber_sum_eq_selected hell cut a u m hlower hupper

theorem monomial_actual_eq_ideal
    (hell : 0 < ell)
    (u : Encoding.Node ell)
    (m : Fin (Encoding.variableCount ell) →₀ ℕ)
    (x : ORInput ell)
    (hmdegree : m.sum (fun _ exponent ↦ exponent) ≤ k)
    (hsmall :
      2 * k + rowLocalitySlack < BinaryPointer.order ell) :
    actualMonomialAverage hell u m x =
      idealMonomialAverage hell u m x := by
  obtain ⟨cut, hlower, hupper⟩ :=
    exists_monomial_untouched_cut m hmdegree hsmall
  letI : Nonempty (RowPermSeed (BinaryPointer.order ell)) :=
    ⟨identitySeed (BinaryPointer.order ell)⟩
  letI : Nonempty ↑(activeLabels hell x) :=
    ⟨⟨zeroLabel hell, by simp⟩⟩
  rw [idealMonomialAverage, finiteAverage_comm]
  calc
    actualMonomialAverage hell u m x =
        finiteAverage
          (fun _a : ↑(activeLabels hell x) ↦
            actualMonomialAverage hell u m x) :=
      (finiteAverage_const (actualMonomialAverage hell u m x)).symm
    _ = finiteAverage
          (fun a : ↑(activeLabels hell x) ↦
            finiteAverage fun seed : RowPermSeed (BinaryPointer.order ell) ↦
              if pathEndpoint hell seed a.1 = u then
                monomialValue m (reductionAssignment hell seed x)
              else 0) := by
      apply finiteAverage_congr
      intro a
      exact actualMonomialAverage_eq_selectedAverage
        hell cut a u m hlower hupper

theorem evalBoolean_sinkPolynomial_eq_endpoint_sum
    {Qsharp : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (hell : 0 < ell)
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (endpoint : Encoding.Node ell)
    (y : Fin (Encoding.variableCount ell) → F2) :
    evalBoolean y (sinkPolynomial certSharp endpoint) =
      ∑ u : Encoding.Node ell,
        ∑ m ∈ (sinkPolynomial certSharp u).support,
          (sinkPolynomial certSharp u).coeff m *
            (if endpoint = u then monomialValue m y else 0) := by
  classical
  calc
    evalBoolean y (sinkPolynomial certSharp endpoint) =
        ∑ m ∈ (sinkPolynomial certSharp endpoint).support,
          (sinkPolynomial certSharp endpoint).coeff m * monomialValue m y :=
      evalBoolean_eq_sum_monomialValue _ _
    _ = ∑ u : Encoding.Node ell,
          ∑ m ∈ (sinkPolynomial certSharp u).support,
            (sinkPolynomial certSharp u).coeff m *
              (if endpoint = u then monomialValue m y else 0) := by
      symm
      calc
        (∑ u : Encoding.Node ell,
            ∑ m ∈ (sinkPolynomial certSharp u).support,
              (sinkPolynomial certSharp u).coeff m *
                (if endpoint = u then monomialValue m y else 0)) =
            ∑ m ∈ (sinkPolynomial certSharp endpoint).support,
              (sinkPolynomial certSharp endpoint).coeff m *
                (if endpoint = endpoint then monomialValue m y else 0) := by
          apply Fintype.sum_eq_single endpoint
          intro u hne
          have hne' : endpoint ≠ u := Ne.symm hne
          simp [hne']
        _ = ∑ m ∈ (sinkPolynomial certSharp endpoint).support,
              (sinkPolynomial certSharp endpoint).coeff m * monomialValue m y := by
          simp

theorem finiteActualAverage_eq_sum_monomialAverages
    (hell : 0 < ell)
    {Qsharp : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    finiteActualAverage hell certSharp x =
      ∑ u : Encoding.Node ell,
        ∑ m ∈ (sinkPolynomial certSharp u).support,
          (sinkPolynomial certSharp u).coeff m *
            actualMonomialAverage hell u m x := by
  change finiteAverage
      (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        evalBoolean (reductionAssignment hell seed x)
          (sinkPolynomial certSharp (plantedSink hell seed))) = _
  calc
    finiteAverage
        (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
          evalBoolean (reductionAssignment hell seed x)
            (sinkPolynomial certSharp (plantedSink hell seed))) =
        finiteAverage
          (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
            ∑ u : Encoding.Node ell,
              ∑ m ∈ (sinkPolynomial certSharp u).support,
                (sinkPolynomial certSharp u).coeff m *
                  (if plantedSink hell seed = u then
                    monomialValue m (reductionAssignment hell seed x)
                  else 0)) := by
      apply finiteAverage_congr
      intro seed
      exact evalBoolean_sinkPolynomial_eq_endpoint_sum
        hell certSharp (plantedSink hell seed) (reductionAssignment hell seed x)
    _ = ∑ u : Encoding.Node ell,
          finiteAverage
            (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
              ∑ m ∈ (sinkPolynomial certSharp u).support,
                (sinkPolynomial certSharp u).coeff m *
                  (if plantedSink hell seed = u then
                    monomialValue m (reductionAssignment hell seed x)
                  else 0)) := by
      exact finiteAverage_fintype_sum _
    _ = ∑ u : Encoding.Node ell,
          ∑ m ∈ (sinkPolynomial certSharp u).support,
            finiteAverage
              (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
                (sinkPolynomial certSharp u).coeff m *
                  (if plantedSink hell seed = u then
                    monomialValue m (reductionAssignment hell seed x)
                  else 0)) := by
      apply Finset.sum_congr rfl
      intro u _hu
      exact finiteAverage_finset_sum _ _
    _ = ∑ u : Encoding.Node ell,
          ∑ m ∈ (sinkPolynomial certSharp u).support,
            (sinkPolynomial certSharp u).coeff m *
              actualMonomialAverage hell u m x := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro m _hm
      rw [finiteAverage_const_mul]
      rfl

theorem idealValue_eq_sum_monomialAverages
    (hell : 0 < ell)
    {Qsharp : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (x : ORInput ell) :
    idealValue hell certSharp x =
      ∑ u : Encoding.Node ell,
        ∑ m ∈ (sinkPolynomial certSharp u).support,
          (sinkPolynomial certSharp u).coeff m *
            idealMonomialAverage hell u m x := by
  change finiteAverage
      (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
        finiteAverage fun a : ↑(activeLabels hell x) ↦
          evalBoolean (reductionAssignment hell seed x)
            (sinkPolynomial certSharp (pathEndpoint hell seed a.1))) = _
  calc
    finiteAverage
        (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
          finiteAverage fun a : ↑(activeLabels hell x) ↦
            evalBoolean (reductionAssignment hell seed x)
              (sinkPolynomial certSharp (pathEndpoint hell seed a.1))) =
        finiteAverage
          (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
            finiteAverage fun a : ↑(activeLabels hell x) ↦
              ∑ u : Encoding.Node ell,
                ∑ m ∈ (sinkPolynomial certSharp u).support,
                  (sinkPolynomial certSharp u).coeff m *
                    (if pathEndpoint hell seed a.1 = u then
                      monomialValue m (reductionAssignment hell seed x)
                    else 0)) := by
      apply finiteAverage_congr
      intro seed
      apply finiteAverage_congr
      intro a
      exact evalBoolean_sinkPolynomial_eq_endpoint_sum hell certSharp
        (pathEndpoint hell seed a.1) (reductionAssignment hell seed x)
    _ = ∑ u : Encoding.Node ell,
          finiteAverage
            (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
              finiteAverage fun a : ↑(activeLabels hell x) ↦
                ∑ m ∈ (sinkPolynomial certSharp u).support,
                  (sinkPolynomial certSharp u).coeff m *
                    (if pathEndpoint hell seed a.1 = u then
                      monomialValue m (reductionAssignment hell seed x)
                    else 0)) := by
      exact finiteAverage₂_fintype_sum _
    _ = ∑ u : Encoding.Node ell,
          ∑ m ∈ (sinkPolynomial certSharp u).support,
            finiteAverage
              (fun seed : RowPermSeed (BinaryPointer.order ell) ↦
                finiteAverage fun a : ↑(activeLabels hell x) ↦
                  (sinkPolynomial certSharp u).coeff m *
                    (if pathEndpoint hell seed a.1 = u then
                      monomialValue m (reductionAssignment hell seed x)
                    else 0)) := by
      apply Finset.sum_congr rfl
      intro u _hu
      exact finiteAverage₂_finset_sum _ _
    _ = ∑ u : Encoding.Node ell,
          ∑ m ∈ (sinkPolynomial certSharp u).support,
            (sinkPolynomial certSharp u).coeff m *
              idealMonomialAverage hell u m x := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro m _hm
      rw [finiteAverage₂_const_mul]
      rfl

theorem actual_eq_ideal
    {ell k : ℕ} (hell : 0 < ell)
    {Qsharp : (Fin (Encoding.variableCount ell) → F2) → ℝ}
    (certSharp : NSCertificate (Encoding.searchCNF ell hell) Qsharp)
    (hdegree : certSharp.DegreeLE k)
    (hsmall :
      2 * k + rowLocalitySlack < BinaryPointer.order ell)
    (x : ORInput ell) :
    evalBoolean x (actualPolynomial hell certSharp) =
      idealValue hell certSharp x := by
  rw [evalBoolean_actualPolynomial,
    finiteActualAverage_eq_sum_monomialAverages,
    idealValue_eq_sum_monomialAverages]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro m hm
  rw [monomial_actual_eq_ideal hell u m x
    ((MvPolynomial.le_totalDegree hm).trans
      (totalDegree_sinkPolynomial_le_of_degreeLE hdegree u)) hsmall]

end ApproxNS

end SoPL

end Revres
