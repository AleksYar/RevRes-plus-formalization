import Revres.DecisionTree.Polynomial
import Revres.Polynomial.Normalization

/-!
# Decision-tree transfer of semantic Nullstellensatz certificates

A bounded-depth formulation maps target variables to source decision trees and searches for a
falsified source clause whenever a target clause is falsified. Leaf cubes turn this semantic
search into polynomial source-clause multipliers.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace Term

variable {M : ℕ}

/-- The clause whose falsifying partial assignment is a canonical term. -/
def toClause (t : Term M) : Clause M :=
  t.val

@[simp]
theorem toClause_falsified_iff (t : Term M) (y : Fin M → F2) :
    t.toClause.Falsified y ↔ t.Matches y :=
  Iff.rfl

@[simp]
theorem support_toClause (t : Term M) :
    t.toClause.support = t.support :=
  rfl

@[simp]
theorem width_toClause (t : Term M) :
    t.toClause.width = t.degree :=
  rfl

theorem matches_completion (t : Term M) :
    t.Matches t.completion := by
  intro i b hib
  simp [completion, hib]

end Term

namespace DecisionTree

universe u

variable {M : ℕ} {alpha : Type u} {T : DecisionTree M alpha}

namespace LeafPath

noncomputable local instance leafMatchesDecidable
    (leaf : T.LeafPath) (y : Fin M → F2) : Decidable (leaf.Matches y) :=
  Classical.propDecidable _

theorem card_queriedVars_le_length (leaf : T.LeafPath) :
    leaf.queriedVars.card ≤ leaf.length := by
  induction leaf with
  | leaf => simp
  | @zero i zeroTree oneTree leaf ih =>
      change (insert i leaf.queriedVars).card ≤ 1 + leaf.length
      calc
        (insert i leaf.queriedVars).card ≤ leaf.queriedVars.card + 1 :=
          Finset.card_insert_le i leaf.queriedVars
        _ ≤ leaf.length + 1 := Nat.add_le_add_right ih 1
        _ = 1 + leaf.length := Nat.add_comm _ _
  | @one i zeroTree oneTree leaf ih =>
      change (insert i leaf.queriedVars).card ≤ 1 + leaf.length
      calc
        (insert i leaf.queriedVars).card ≤ leaf.queriedVars.card + 1 :=
          Finset.card_insert_le i leaf.queriedVars
        _ ≤ leaf.length + 1 := Nat.add_le_add_right ih 1
        _ = 1 + leaf.length := Nat.add_comm _ _

/-- The polynomial indicator of a reachable leaf cube; contradictory paths contribute zero. -/
noncomputable def indicatorPolynomial (leaf : T.LeafPath) : BooleanPolynomial M :=
  match DecisionTree.leafPartialAssignment leaf with
  | none => 0
  | some t => t.toClause.clausePolynomial

@[simp]
theorem evalBoolean_indicatorPolynomial (leaf : T.LeafPath) (y : Fin M → F2) :
    evalBoolean y leaf.indicatorPolynomial = if leaf.Matches y then 1 else 0 := by
  classical
  cases hterm : DecisionTree.leafPartialAssignment leaf with
  | none =>
      have hnot := leaf.not_matches_of_leafPartialAssignment_eq_none hterm y
      simp [indicatorPolynomial, hterm, hnot]
  | some t =>
      rw [indicatorPolynomial, hterm, Clause.clausePolynomial_evalBoolean_eq_if]
      have heq : t.toClause.Falsified y ↔ leaf.Matches y :=
        (Term.toClause_falsified_iff t y).trans
          (leaf.matches_iff_of_leafPartialAssignment_eq_some hterm y).symm
      by_cases hleaf : leaf.Matches y
      · rw [if_pos (heq.mpr hleaf), if_pos hleaf]
      · rw [if_neg (fun hfalse ↦ hleaf (heq.mp hfalse)), if_neg hleaf]

theorem totalDegree_indicatorPolynomial_le_length (leaf : T.LeafPath) :
    leaf.indicatorPolynomial.totalDegree ≤ leaf.length := by
  cases hterm : DecisionTree.leafPartialAssignment leaf with
  | none => simp [indicatorPolynomial, hterm]
  | some t =>
      rw [indicatorPolynomial, hterm, Clause.totalDegree_clausePolynomial_eq,
        Term.width_toClause]
      change t.support.card ≤ leaf.length
      rw [leaf.support_of_leafPartialAssignment_eq_some hterm]
      exact leaf.card_queriedVars_le_length

theorem totalDegree_indicatorPolynomial_le_depth (leaf : T.LeafPath) :
    leaf.indicatorPolynomial.totalDegree ≤ T.depth :=
  leaf.totalDegree_indicatorPolynomial_le_length.trans leaf.length_le_depth

end LeafPath

end DecisionTree

namespace Clause

variable {M : ℕ} {t : Term M} {D : Clause M}

theorem support_subset_term_support_of_matches_imp_falsified
    (h : ∀ y, t.Matches y → D.Falsified y) :
    D.support ⊆ t.support := by
  intro i hiD
  obtain ⟨b, hib⟩ := Clause.exists_eq_some_of_mem_support hiD
  by_contra hit
  have ht_none : t.val i = none := Term.not_mem_support.mp hit
  let y : Fin M → F2 := fun j ↦ if j = i then b + 1 else t.completion j
  have hy_matches : t.Matches y := by
    intro j c hjc
    have hji : j ≠ i := by
      intro hji
      subst j
      simp [ht_none] at hjc
    simp [y, hji, t.matches_completion j c hjc]
  have hy_falsified := h y hy_matches
  have hyi := hy_falsified i b hib
  have hne : b + 1 ≠ b :=
    (F2_ne_iff_eq_add_one (b + 1) b).2 rfl
  simp only [y, if_pos rfl] at hyi
  exact hne hyi

theorem width_le_term_degree_of_matches_imp_falsified
    (h : ∀ y, t.Matches y → D.Falsified y) :
    D.width ≤ t.degree := by
  rw [Clause.width, Term.degree]
  exact Finset.card_le_card
    (support_subset_term_support_of_matches_imp_falsified h)

theorem width_le_leaf_length
    {alpha : Type*} {T : DecisionTree M alpha} {leaf : T.LeafPath}
    {t : Term M} {D : Clause M}
    (hterm : DecisionTree.leafPartialAssignment leaf = some t)
    (hD : ∀ y, leaf.Matches y → D.Falsified y) :
    D.width ≤ leaf.length := by
  have hwidth : D.width ≤ t.degree :=
    width_le_term_degree_of_matches_imp_falsified (t := t) (D := D) (by
      intro y hy
      exact hD y ((leaf.matches_iff_of_leafPartialAssignment_eq_some hterm y).mpr hy))
  have hdegree : t.degree ≤ leaf.length := by
    rw [Term.degree, leaf.support_of_leafPartialAssignment_eq_some hterm]
    exact leaf.card_queriedVars_le_length
  exact hwidth.trans hdegree

end Clause

/-- A bounded-depth decision-tree reduction from target clauses to source clauses. -/
structure DTFormulation {M N : ℕ} (G : CNF M) (F : CNF N) where
  depth : ℕ
  inputTree : Fin N → DecisionTree M F2
  inputTree_depth : ∀ i, (inputTree i).depth ≤ depth
  clauseSearch : (C : ↑F) → DecisionTree M (Option (Clause M))
  clauseSearch_depth : ∀ C, (clauseSearch C).depth ≤ C.1.width * depth
  clauseSearch_sound :
    ∀ C y D,
      (clauseSearch C).eval y = some D →
        D ∈ G ∧ D.Falsified y ∧
          C.1.Falsified (fun i ↦ (inputTree i).eval y)
  clauseSearch_complete :
    ∀ C y,
      C.1.Falsified (fun i ↦ (inputTree i).eval y) →
        ∃ D, (clauseSearch C).eval y = some D

namespace DTFormulation

variable {M N : ℕ} {G : CNF M} {F : CNF N}

/-- The target assignment computed by the input decision trees. -/
def mapInput (rho : DTFormulation G F) (y : Fin M → F2) : Fin N → F2 :=
  fun i ↦ (rho.inputTree i).eval y

/-- The polynomial representing one mapped target input bit. -/
noncomputable def inputPolynomial
    (rho : DTFormulation G F) (i : Fin N) : BooleanPolynomial M :=
  (rho.inputTree i).polynomial f2ToReal

@[simp]
theorem evalBoolean_inputPolynomial
    (rho : DTFormulation G F) (i : Fin N) (y : Fin M → F2) :
    evalBoolean y (rho.inputPolynomial i) = f2ToReal (rho.mapInput y i) := by
  simp [inputPolynomial, mapInput]

theorem totalDegree_inputPolynomial_le
    (rho : DTFormulation G F) (i : Fin N) :
    (rho.inputPolynomial i).totalDegree ≤ rho.depth :=
  (rho.inputTree i).totalDegree_polynomial_le_depth f2ToReal |>.trans
    (rho.inputTree_depth i)

/-- Substitute the decision-tree polynomials for all target variables. -/
noncomputable def polynomialMap (rho : DTFormulation G F) :
    BooleanPolynomial N →ₐ[ℝ] BooleanPolynomial M :=
  MvPolynomial.bind₁ rho.inputPolynomial

@[simp]
theorem polynomialMap_C (rho : DTFormulation G F) (r : ℝ) :
    rho.polynomialMap (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [polynomialMap]

@[simp]
theorem polynomialMap_X (rho : DTFormulation G F) (i : Fin N) :
    rho.polynomialMap (MvPolynomial.X i) = rho.inputPolynomial i := by
  simp [polynomialMap]

theorem evalBoolean_polynomialMap
    (rho : DTFormulation G F) (p : BooleanPolynomial N) (y : Fin M → F2) :
    evalBoolean y (rho.polynomialMap p) = evalBoolean (rho.mapInput y) p := by
  change
    MvPolynomial.aeval (fun i ↦ f2ToReal (y i))
        (MvPolynomial.bind₁ rho.inputPolynomial p) =
      MvPolynomial.aeval (fun i ↦ f2ToReal (rho.mapInput y i)) p
  rw [MvPolynomial.aeval_bind₁]
  apply congrArg (fun values : Fin N → ℝ ↦ MvPolynomial.aeval values p)
  funext i
  exact rho.evalBoolean_inputPolynomial i y

theorem totalDegree_polynomialMap_le
    (rho : DTFormulation G F) (p : BooleanPolynomial N) :
    (rho.polynomialMap p).totalDegree ≤ p.totalDegree * rho.depth := by
  classical
  have hsum :
      rho.polynomialMap p =
        ∑ d ∈ p.support,
          rho.polynomialMap (MvPolynomial.monomial d (p.coeff d)) := by
    rw [← map_sum, ← p.as_sum]
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [polynomialMap, MvPolynomial.bind₁_monomial]
  calc
    (MvPolynomial.C (p.coeff d) *
        ∏ i ∈ d.support, rho.inputPolynomial i ^ d i).totalDegree ≤
        (∏ i ∈ d.support, rho.inputPolynomial i ^ d i).totalDegree := by
      simpa using MvPolynomial.totalDegree_mul
        (MvPolynomial.C (p.coeff d))
        (∏ i ∈ d.support, rho.inputPolynomial i ^ d i)
    _ ≤ ∑ i ∈ d.support, (rho.inputPolynomial i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd d.support
        (fun i ↦ rho.inputPolynomial i ^ d i)
    _ ≤ ∑ i ∈ d.support, d i * rho.depth := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (MvPolynomial.totalDegree_pow (rho.inputPolynomial i) (d i)).trans
        (Nat.mul_le_mul_left (d i) (rho.totalDegree_inputPolynomial_le i))
    _ = (d.sum fun _ e ↦ e) * rho.depth := by
      rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * rho.depth :=
      Nat.mul_le_mul_right rho.depth (MvPolynomial.le_totalDegree hd)

/-- Sum the indicators of all search-leaf occurrences labeled by a fixed source clause. -/
noncomputable def clauseMultiplier
    (rho : DTFormulation G F) (C : ↑F) (D : Clause M) : BooleanPolynomial M :=
  ∑ leaf : (rho.clauseSearch C).LeafPath,
    if leaf.value = some D then leaf.indicatorPolynomial else 0

@[simp]
theorem evalBoolean_clauseMultiplier
    (rho : DTFormulation G F) (C : ↑F) (D : Clause M) (y : Fin M → F2) :
    evalBoolean y (rho.clauseMultiplier C D) =
      if (rho.clauseSearch C).eval y = some D then 1 else 0 := by
  classical
  rw [clauseMultiplier, evalBoolean_finset_sum]
  let reached := (rho.clauseSearch C).reachedLeaf y
  rw [Finset.sum_eq_single reached]
  · have hmatch : reached.Matches y := (rho.clauseSearch C).reachedLeaf_matches y
    have heval : (rho.clauseSearch C).eval y = reached.value :=
      DecisionTree.eval_eq_leafValue_of_matches reached hmatch
    by_cases hvalue : reached.value = some D
    · simp [hvalue, hmatch, heval]
    · simp [hvalue, heval]
  · intro leaf _hleaf hne
    have hnot : ¬leaf.Matches y := by
      intro hmatch
      exact hne (leaf.eq_reachedLeaf_of_matches hmatch)
    by_cases hvalue : leaf.value = some D
    · rw [if_pos hvalue, leaf.evalBoolean_indicatorPolynomial, if_neg hnot]
    · rw [if_neg hvalue, evalBoolean_zero]
  · simp

theorem totalDegree_clauseMultiplier_mul_le
    (rho : DTFormulation G F) (C : ↑F) (D : Clause M) :
    (rho.clauseMultiplier C D * D.clausePolynomial).totalDegree ≤
      2 * C.1.width * rho.depth := by
  classical
  rw [clauseMultiplier, Finset.sum_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro leaf _hleaf
  by_cases hvalue : leaf.value = some D
  · rw [if_pos hvalue]
    cases hterm : DecisionTree.leafPartialAssignment leaf with
    | none => simp [DecisionTree.LeafPath.indicatorPolynomial, hterm]
    | some t =>
        have hD : ∀ y, leaf.Matches y → D.Falsified y := by
          intro y hmatch
          have heval : (rho.clauseSearch C).eval y = some D :=
            (DecisionTree.eval_eq_leafValue_of_matches leaf hmatch).trans hvalue
          exact (rho.clauseSearch_sound C y D heval).2.1
        have hwidth : D.width ≤ leaf.length :=
          Clause.width_le_leaf_length hterm hD
        calc
          (leaf.indicatorPolynomial * D.clausePolynomial).totalDegree ≤
              leaf.indicatorPolynomial.totalDegree +
                D.clausePolynomial.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ leaf.length + D.width := Nat.add_le_add
            leaf.totalDegree_indicatorPolynomial_le_length
            (Clause.totalDegree_clausePolynomial_le D)
          _ ≤ 2 * leaf.length := by omega
          _ ≤ 2 * (rho.clauseSearch C).depth :=
            Nat.mul_le_mul_left 2 leaf.length_le_depth
          _ ≤ 2 * (C.1.width * rho.depth) :=
            Nat.mul_le_mul_left 2 (rho.clauseSearch_depth C)
          _ = 2 * C.1.width * rho.depth := (Nat.mul_assoc _ _ _).symm
  · simp [hvalue]

theorem clause_transfer_identity
    (rho : DTFormulation G F) (C : ↑F) (y : Fin M → F2) :
    evalBoolean (rho.mapInput y) C.1.clausePolynomial =
      polynomialAxiomCombination G (rho.clauseMultiplier C) y := by
  classical
  rw [Clause.clausePolynomial_evalBoolean_eq_if]
  unfold polynomialAxiomCombination
  simp_rw [evalBoolean_mul, rho.evalBoolean_clauseMultiplier,
    Clause.clausePolynomial_evalBoolean_eq_if]
  by_cases hC : C.1.Falsified (rho.mapInput y)
  · rw [if_pos hC]
    obtain ⟨D, hDvalue⟩ := rho.clauseSearch_complete C y hC
    obtain ⟨hDG, hDfalsified, _⟩ := rho.clauseSearch_sound C y D hDvalue
    rw [Finset.sum_eq_single D]
    · simp [hDvalue, hDfalsified]
    · intro E hEG hED
      have hEvalue : (rho.clauseSearch C).eval y ≠ some E := by
        intro h
        have : D = E := by simpa [hDvalue] using h
        exact hED this.symm
      simp [hEvalue]
    · simp [hDG]
  · rw [if_neg hC]
    symm
    apply Finset.sum_eq_zero
    intro D hDG
    have hDvalue : (rho.clauseSearch C).eval y ≠ some D := by
      intro h
      exact hC (rho.clauseSearch_sound C y D h).2.2
    simp [hDvalue]

/-- The semantic source certificate obtained from one target clause. -/
noncomputable def clauseCertificate
    (rho : DTFormulation G F) (C : ↑F) :
    NSCertificate G
      (fun y ↦ evalBoolean (rho.mapInput y) C.1.clausePolynomial) where
  multiplier := rho.clauseMultiplier C
  represents := rho.clause_transfer_identity C

theorem clauseCertificate_degree_le
    (rho : DTFormulation G F) (C : ↑F) :
    (rho.clauseCertificate C).degree ≤ 2 * C.1.width * rho.depth := by
  change (rho.clauseCertificate C).DegreeLE (2 * C.1.width * rho.depth)
  rw [NSCertificate.degree_le_iff]
  intro D _hDG
  exact rho.totalDegree_clauseMultiplier_mul_le C D

/-- The source multiplier obtained by distributing all normalized target-clause contributions. -/
noncomputable def transferredMultiplier
    (rho : DTFormulation G F)
    {P : (Fin N → F2) → ℝ} (cert : NSCertificate F P)
    (D : Clause M) : BooleanPolynomial M :=
  ∑ C : ↑F,
    rho.polynomialMap (cert.normalize.multiplier C.1) *
      rho.clauseMultiplier C D

theorem transferredMultiplier_represents
    (rho : DTFormulation G F)
    {P : (Fin N → F2) → ℝ} (cert : NSCertificate F P)
    (y : Fin M → F2) :
    P (rho.mapInput y) =
      polynomialAxiomCombination G (rho.transferredMultiplier cert) y := by
  calc
    P (rho.mapInput y) =
        polynomialAxiomCombination F cert.normalize.multiplier (rho.mapInput y) :=
      cert.normalize.represents (rho.mapInput y)
    _ = ∑ C : ↑F,
        evalBoolean (rho.mapInput y)
          (cert.normalize.multiplier C.1 * C.1.clausePolynomial) := by
      unfold polynomialAxiomCombination
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
    _ = ∑ C : ↑F,
        evalBoolean y (rho.polynomialMap (cert.normalize.multiplier C.1)) *
          polynomialAxiomCombination G (rho.clauseMultiplier C) y := by
      apply Finset.sum_congr rfl
      intro C _hC
      rw [evalBoolean_mul, ← rho.evalBoolean_polynomialMap,
        rho.clause_transfer_identity]
    _ = ∑ C : ↑F, ∑ D ∈ G,
        evalBoolean y
          ((rho.polynomialMap (cert.normalize.multiplier C.1) *
              rho.clauseMultiplier C D) * D.clausePolynomial) := by
      apply Finset.sum_congr rfl
      intro C _hC
      unfold polynomialAxiomCombination
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _hDG
      simp only [evalBoolean_mul]
      rw [mul_assoc]
    _ = ∑ D ∈ G, ∑ C : ↑F,
        evalBoolean y
          ((rho.polynomialMap (cert.normalize.multiplier C.1) *
              rho.clauseMultiplier C D) * D.clausePolynomial) := by
      rw [Finset.sum_comm]
    _ = polynomialAxiomCombination G (rho.transferredMultiplier cert) y := by
      unfold polynomialAxiomCombination
      apply Finset.sum_congr rfl
      intro D _hDG
      rw [transferredMultiplier, Finset.sum_mul, evalBoolean_finset_sum]

end DTFormulation

namespace NSCertificate

variable {M N : ℕ} {G : CNF M} {F : CNF N}
  {P : (Fin N → F2) → ℝ}

/-- Transfer a semantic certificate through a bounded-depth decision-tree formulation. -/
noncomputable def transfer
    (cert : NSCertificate F P) (rho : DTFormulation G F) :
    NSCertificate G (fun y ↦ P (rho.mapInput y)) where
  multiplier := rho.transferredMultiplier cert
  represents := rho.transferredMultiplier_represents cert

private theorem normalize_multiplier_degree_add_width_le
    (cert : NSCertificate F P) (C : ↑F)
    (hnonzero : cert.normalize.multiplier C.1 ≠ 0) :
    (cert.normalize.multiplier C.1).totalDegree + C.1.width ≤ cert.degree := by
  have hproduct :
      (cert.normalize.multiplier C.1 * C.1.clausePolynomial).totalDegree ≤
        cert.normalize.degree :=
    (degree_le_iff.mp
      (show cert.normalize.DegreeLE cert.normalize.degree from le_rfl)) C.1 C.2
  calc
    (cert.normalize.multiplier C.1).totalDegree + C.1.width =
        (cert.normalize.multiplier C.1).totalDegree +
          C.1.clausePolynomial.totalDegree := by
      rw [Clause.totalDegree_clausePolynomial_eq]
    _ = (cert.normalize.multiplier C.1 * C.1.clausePolynomial).totalDegree :=
      (MvPolynomial.totalDegree_mul_of_isDomain hnonzero
        (Clause.clausePolynomial_ne_zero C.1)).symm
    _ ≤ cert.normalize.degree := hproduct
    _ ≤ cert.degree := cert.normalize_degree_le

theorem transfer_degree_le
    (cert : NSCertificate F P) (rho : DTFormulation G F) :
    (cert.transfer rho).degree ≤ 2 * cert.degree * rho.depth := by
  change (cert.transfer rho).DegreeLE (2 * cert.degree * rho.depth)
  rw [degree_le_iff]
  intro D _hDG
  change
    (rho.transferredMultiplier cert D * D.clausePolynomial).totalDegree ≤
      2 * cert.degree * rho.depth
  rw [DTFormulation.transferredMultiplier, Finset.sum_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro C _hC
  by_cases hzero : cert.normalize.multiplier C.1 = 0
  · rw [hzero, map_zero]
    simp
  · rw [mul_assoc]
    calc
      (rho.polynomialMap (cert.normalize.multiplier C.1) *
          (rho.clauseMultiplier C D * D.clausePolynomial)).totalDegree ≤
          (rho.polynomialMap
              (cert.normalize.multiplier C.1)).totalDegree +
            (rho.clauseMultiplier C D *
              D.clausePolynomial).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (cert.normalize.multiplier C.1).totalDegree * rho.depth +
          2 * C.1.width * rho.depth :=
        Nat.add_le_add
          (rho.totalDegree_polynomialMap_le (cert.normalize.multiplier C.1))
          (rho.totalDegree_clauseMultiplier_mul_le C D)
      _ = ((cert.normalize.multiplier C.1).totalDegree +
            2 * C.1.width) * rho.depth := by
        rw [Nat.add_mul, Nat.mul_assoc]
      _ ≤ (2 * ((cert.normalize.multiplier C.1).totalDegree +
            C.1.width)) * rho.depth := by
        apply Nat.mul_le_mul_right rho.depth
        omega
      _ ≤ (2 * cert.degree) * rho.depth := by
        apply Nat.mul_le_mul_right rho.depth
        exact Nat.mul_le_mul_left 2
          (normalize_multiplier_degree_add_width_le cert C hzero)
      _ = 2 * cert.degree * rho.depth := rfl

end NSCertificate

theorem clause_transfer
    {M N : ℕ} {G : CNF M} {F : CNF N}
    (rho : DTFormulation G F) (C : ↑F) :
    HasNSCertificateDegreeLE G
      (fun y ↦ evalBoolean (rho.mapInput y) C.1.clausePolynomial)
      (2 * C.1.width * rho.depth) :=
  ⟨rho.clauseCertificate C, rho.clauseCertificate_degree_le C⟩

theorem certificate_transfer
    {M N : ℕ} {G : CNF M} {F : CNF N}
    {P : (Fin N → F2) → ℝ}
    (rho : DTFormulation G F) (cert : NSCertificate F P) :
    ∃ cert' : NSCertificate G (fun y ↦ P (rho.mapInput y)),
      cert'.degree ≤ 2 * cert.degree * rho.depth :=
  ⟨cert.transfer rho, cert.transfer_degree_le rho⟩

theorem hasCertificateDegreeLE_transfer
    {M N degree : ℕ} {G : CNF M} {F : CNF N}
    {P : (Fin N → F2) → ℝ}
    (rho : DTFormulation G F)
    (h : HasNSCertificateDegreeLE F P degree) :
    HasNSCertificateDegreeLE G
      (fun y ↦ P (rho.mapInput y))
      (2 * degree * rho.depth) := by
  obtain ⟨cert, hdegree⟩ := h
  refine ⟨cert.transfer rho, (cert.transfer_degree_le rho).trans ?_⟩
  exact Nat.mul_le_mul_right rho.depth (Nat.mul_le_mul_left 2 hdegree)

end Revres
