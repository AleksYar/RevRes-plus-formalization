import Revres.LowerBound.Finite
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit subsequence parameters

This file chooses an integer subsequence for the finite lower bound and records
the exact arithmetic needed by the conditional family theorem.
-/

namespace Revres

open Filter Asymptotics

/-- Shift the family parameter past all finite exceptional cases. -/
def subsequenceShift (t : ℕ) : ℕ :=
  t + 6

/-- Pointer width on the explicit subsequence. -/
def subsequenceEll (t : ℕ) : ℕ :=
  8 * subsequenceShift t

/-- Junta degree used in the robust decomposition. -/
def subsequenceDegree (t : ℕ) : ℕ :=
  2 ^ subsequenceShift t

/-- Degree up to which support-local SoPL hardness is assumed. -/
def subsequenceHardnessDegree (t : ℕ) : ℕ :=
  2 ^ (4 * subsequenceShift t)

theorem subsequenceShift_six_le (t : ℕ) :
    6 ≤ subsequenceShift t := by
  simp [subsequenceShift]

theorem subsequenceEll_pos (t : ℕ) :
    0 < subsequenceEll t := by
  simp [subsequenceEll, subsequenceShift]

theorem subsequenceEll_strictMono :
    StrictMono subsequenceEll := by
  intro a b hab
  simp only [subsequenceEll, subsequenceShift]
  omega

theorem subsequenceDegree_eq (t : ℕ) :
    subsequenceDegree t = 2 ^ subsequenceShift t :=
  rfl

theorem subsequence_localOrder_add_one (t : ℕ) :
    SoD.ActiveEdge.localOrder (subsequenceEll t) + 1 =
      (subsequenceDegree t) ^ 8 := by
  rw [BinaryPointer.order_add_one]
  simp only [subsequenceEll, subsequenceDegree]
  rw [show 8 * subsequenceShift t = subsequenceShift t * 8 by omega, pow_mul]

theorem subsequence_localOrder_gt_one (t : ℕ) :
    1 < SoD.ActiveEdge.localOrder (subsequenceEll t) := by
  have hpow : 4 ≤ 2 ^ subsequenceEll t := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ subsequenceEll t := by
        exact Nat.pow_le_pow_right (by norm_num) (by
          simp only [subsequenceEll, subsequenceShift]
          omega)
  unfold SoD.ActiveEdge.localOrder BinaryPointer.order
  omega

private theorem smallDegree_numeric
    (s : ℕ) (hs : 6 ≤ s) :
    3200 * s * 2 ^ s < 2 ^ (8 * s) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        3200 * (s + 1) * 2 ^ (s + 1) =
            2 * (3200 * (s + 1) * 2 ^ s) := by
          rw [pow_succ]
          ring
        _ ≤ 4 * (3200 * s * 2 ^ s) := by
          have hlinear : 2 * (s + 1) ≤ 4 * s := by omega
          calc
            2 * (3200 * (s + 1) * 2 ^ s) =
                (2 * (s + 1)) * (3200 * 2 ^ s) := by ring
            _ ≤ (4 * s) * (3200 * 2 ^ s) :=
              Nat.mul_le_mul_right (3200 * 2 ^ s) hlinear
            _ = 4 * (3200 * s * 2 ^ s) := by ring
        _ < 4 * 2 ^ (8 * s) :=
          Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ < 256 * 2 ^ (8 * s) := by
          gcongr
          norm_num
        _ = 2 ^ (8 * (s + 1)) := by
          rw [show 8 * (s + 1) = 8 * s + 8 by ring, pow_add]
          norm_num
          ring

private theorem transferDegree_numeric
    (s : ℕ) (hs : 6 ≤ s) :
    3584 * s ^ 2 * 2 ^ s < 2 ^ (4 * s) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        3584 * (s + 1) ^ 2 * 2 ^ (s + 1) =
            2 * (3584 * (s + 1) ^ 2 * 2 ^ s) := by
          rw [pow_succ]
          ring
        _ ≤ 8 * (3584 * s ^ 2 * 2 ^ s) := by
          have hsquare : 2 * (s + 1) ^ 2 ≤ 8 * s ^ 2 := by
            nlinarith
          calc
            2 * (3584 * (s + 1) ^ 2 * 2 ^ s) =
                (2 * (s + 1) ^ 2) * (3584 * 2 ^ s) := by ring
            _ ≤ (8 * s ^ 2) * (3584 * 2 ^ s) :=
              Nat.mul_le_mul_right (3584 * 2 ^ s) hsquare
            _ = 8 * (3584 * s ^ 2 * 2 ^ s) := by ring
        _ < 8 * 2 ^ (4 * s) :=
          Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ < 16 * 2 ^ (4 * s) := by
          gcongr
          norm_num
        _ = 2 ^ (4 * (s + 1)) := by
          rw [show 4 * (s + 1) = 4 * s + 4 by ring, pow_add]
          norm_num
          ring

theorem cleaningDegree_eq (ell degree : ℕ) :
    SoD.Preprocess.cleaningDegree ell degree = 4 * degree * ell := by
  simp [SoD.Preprocess.cleaningDegree]
  ring

theorem cleaningCertificateDegree_eq (ell degree : ℕ) :
    SoD.Preprocess.cleaningCertificateDegree ell degree =
      max (4 * ell) (4 * degree * ell) := by
  unfold SoD.Preprocess.cleaningCertificateDegree
  rw [cleaningDegree_eq]
  apply congrArg₂ max
  · ring
  · rfl

theorem subsequence_smallDegree (t : ℕ) :
    100 * SoD.Preprocess.cleaningDegree
        (subsequenceEll t) (subsequenceDegree t) ≤
      SoD.ActiveEdge.localOrder (subsequenceEll t) := by
  have hnumeric := smallDegree_numeric (subsequenceShift t)
    (subsequenceShift_six_le t)
  rw [cleaningDegree_eq]
  unfold subsequenceEll subsequenceDegree SoD.ActiveEdge.localOrder BinaryPointer.order
  have hleft :
      100 * (4 * 2 ^ subsequenceShift t * (8 * subsequenceShift t)) =
        3200 * subsequenceShift t * 2 ^ subsequenceShift t := by ring
  rw [hleft]
  omega

theorem subsequence_transferDegree (t : ℕ) :
    2 * SoD.Preprocess.cleaningCertificateDegree
          (subsequenceEll t) (subsequenceDegree t) *
        (7 * subsequenceEll t) <
      subsequenceHardnessDegree t := by
  have hdegree : 1 ≤ subsequenceDegree t := by
    have hpos : 0 < subsequenceDegree t := by
      exact pow_pos (by norm_num) _
    omega
  have hmax :
      max (4 * subsequenceEll t)
          (4 * subsequenceDegree t * subsequenceEll t) =
        4 * subsequenceDegree t * subsequenceEll t := by
    rw [max_eq_right]
    calc
      4 * subsequenceEll t = 4 * 1 * subsequenceEll t := by ring
      _ ≤ 4 * subsequenceDegree t * subsequenceEll t := by
        exact Nat.mul_le_mul_right (subsequenceEll t)
          (Nat.mul_le_mul_left 4 hdegree)
  have hnumeric := transferDegree_numeric (subsequenceShift t)
    (subsequenceShift_six_le t)
  rw [cleaningCertificateDegree_eq, hmax]
  unfold subsequenceEll subsequenceDegree subsequenceHardnessDegree
  calc
    2 * (4 * 2 ^ subsequenceShift t * (8 * subsequenceShift t)) *
          (7 * (8 * subsequenceShift t)) =
        3584 * (subsequenceShift t) ^ 2 * 2 ^ subsequenceShift t := by ring
    _ < 2 ^ (4 * subsequenceShift t) := hnumeric

/-! ## A natural-power lower scale -/

/-- The positive exponential rate occurring in `decompositionError`. -/
noncomputable def decompositionDecayRate : ℝ :=
  min (Lemma53.κ0 / 4) (1 / 4)

theorem decompositionDecayRate_pos :
    0 < decompositionDecayRate := by
  unfold decompositionDecayRate
  exact lt_min (div_pos Lemma53.κ0_pos (by norm_num)) (by norm_num)

/-- A fixed natural denominator whose reciprocal is below the decay rate. -/
noncomputable def decompositionDecayDenominator : ℕ :=
  Classical.choose (exists_nat_one_div_lt decompositionDecayRate_pos) + 1

theorem decompositionDecayDenominator_pos :
    0 < decompositionDecayDenominator := by
  unfold decompositionDecayDenominator
  omega

theorem one_div_decompositionDecayDenominator_le :
    (1 : ℝ) / decompositionDecayDenominator ≤ decompositionDecayRate := by
  have hchosen :=
    Classical.choose_spec (exists_nat_one_div_lt decompositionDecayRate_pos)
  simpa [decompositionDecayDenominator] using hchosen.le

/-- The public lower scale has only an ordinary natural power of two. -/
noncomputable def subsequenceLengthScale (t : ℕ) : ℝ :=
  (1 / 200 : ℝ) *
    (2 : ℝ) ^ (subsequenceDegree t / decompositionDecayDenominator)

private theorem naturalExponent_le_decayExponent (R : ℕ) :
    ((R / decompositionDecayDenominator : ℕ) : ℝ) ≤
      decompositionDecayRate * (R : ℝ) := by
  have hdenomReal : (0 : ℝ) < decompositionDecayDenominator := by
    exact_mod_cast decompositionDecayDenominator_pos
  have hdivMul :
      R / decompositionDecayDenominator * decompositionDecayDenominator ≤ R :=
    Nat.div_mul_le_self R decompositionDecayDenominator
  have hdivMulReal :
      ((R / decompositionDecayDenominator : ℕ) : ℝ) *
          (decompositionDecayDenominator : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hdivMul
  have hquotient :
      ((R / decompositionDecayDenominator : ℕ) : ℝ) ≤
        (R : ℝ) / decompositionDecayDenominator := by
    exact (le_div_iff₀ hdenomReal).2 hdivMulReal
  calc
    ((R / decompositionDecayDenominator : ℕ) : ℝ) ≤
        (R : ℝ) / decompositionDecayDenominator := hquotient
    _ = ((1 : ℝ) / decompositionDecayDenominator) * (R : ℝ) := by ring
    _ ≤ decompositionDecayRate * (R : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        one_div_decompositionDecayDenominator_le (Nat.cast_nonneg R)

private theorem naturalPower_le_errorQuotient (R : ℕ) :
    (1 / 100 : ℝ) *
        (2 : ℝ) ^ (R / decompositionDecayDenominator) ≤
      SoD.Amplification.errorThreshold / decompositionError R := by
  have hexponent := naturalExponent_le_decayExponent R
  have hrpow :
      (2 : ℝ) ^ (R / decompositionDecayDenominator) ≤
        (2 : ℝ) ^ (decompositionDecayRate * (R : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hinverse :
      (decompositionError R)⁻¹ =
        (2 : ℝ) ^ (decompositionDecayRate * (R : ℝ)) := by
    unfold decompositionError decompositionDecayRate
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  change
    (1 / 100 : ℝ) *
        (2 : ℝ) ^ (R / decompositionDecayDenominator) ≤
      (1 / 100 : ℝ) * (decompositionError R)⁻¹
  rw [hinverse]
  exact mul_le_mul_of_nonneg_left hrpow (by norm_num)

private theorem four_mul_subsequenceDegree_le_localExponent (t : ℕ) :
    4 * subsequenceDegree t ≤
      SoD.ActiveEdge.localOrder (subsequenceEll t) - 1 := by
  let s := subsequenceShift t
  let R := subsequenceDegree t
  let P := 2 ^ (8 * s)
  have hnumeric : 3200 * s * R < P := by
    simpa [s, R, P, subsequenceDegree] using
      smallDegree_numeric (subsequenceShift t) (subsequenceShift_six_le t)
  have hs : 6 ≤ s := by simpa [s] using subsequenceShift_six_le t
  have hR : 1 ≤ R := by
    have hRpos : 0 < R := by
      simp [R, subsequenceDegree]
    omega
  have htwo : 2 ≤ 2 * R := Nat.mul_le_mul_left 2 hR
  have hcoeff : 6 ≤ 3200 * s := by omega
  have hcoarse : 4 * R + 2 ≤ 3200 * s * R := by
    calc
      4 * R + 2 ≤ 4 * R + 2 * R := Nat.add_le_add_left htwo _
      _ = 6 * R := by ring
      _ ≤ (3200 * s) * R := Nat.mul_le_mul_right R hcoeff
  have horder :
      SoD.ActiveEdge.localOrder (subsequenceEll t) = P - 1 := by
    simp [SoD.ActiveEdge.localOrder, BinaryPointer.order, subsequenceEll, P, s]
  rw [horder]
  omega

private theorem naturalPower_le_amplificationGrowth (t : ℕ) :
    (1 / 100 : ℝ) *
        (2 : ℝ) ^
          (subsequenceDegree t / decompositionDecayDenominator) ≤
      (7 / 5 : ℝ) ^
          (SoD.ActiveEdge.localOrder (subsequenceEll t) - 1) - 1 := by
  let R := subsequenceDegree t
  let exponent := SoD.ActiveEdge.localOrder (subsequenceEll t) - 1
  have hRpos : 0 < R := by
    dsimp [R]
    exact pow_pos (by norm_num) _
  have hquotient : R / decompositionDecayDenominator ≤ R :=
    Nat.div_le_self R decompositionDecayDenominator
  have hpowQuotient :
      (2 : ℝ) ^ (R / decompositionDecayDenominator) ≤ (2 : ℝ) ^ R :=
    pow_le_pow_right₀ (by norm_num) hquotient
  have hexponent : 4 * R ≤ exponent := by
    exact four_mul_subsequenceDegree_le_localExponent t
  have hbase : (2 : ℝ) < (7 / 5 : ℝ) ^ 4 := by norm_num
  have hbasePow :
      (2 : ℝ) ^ R < ((7 / 5 : ℝ) ^ 4) ^ R :=
    pow_lt_pow_left₀ hbase (by norm_num) hRpos.ne'
  have hfour :
      ((7 / 5 : ℝ) ^ 4) ^ R = (7 / 5 : ℝ) ^ (4 * R) := by
    rw [← pow_mul]
  have hgrowthPow :
      (2 : ℝ) ^ R < (7 / 5 : ℝ) ^ exponent := by
    rw [hfour] at hbasePow
    exact hbasePow.trans_le (pow_le_pow_right₀ (by norm_num) hexponent)
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ R := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hRpos)
  calc
    (1 / 100 : ℝ) *
        (2 : ℝ) ^ (subsequenceDegree t / decompositionDecayDenominator) =
        (1 / 100 : ℝ) *
          (2 : ℝ) ^ (R / decompositionDecayDenominator) := rfl
    _ ≤ (1 / 100 : ℝ) * (2 : ℝ) ^ R := by
      exact mul_le_mul_of_nonneg_left hpowQuotient (by norm_num)
    _ ≤ (2 : ℝ) ^ R - 1 := by linarith
    _ ≤ (7 / 5 : ℝ) ^ exponent - 1 := by linarith

theorem subsequenceLengthScale_le_finiteScale (t : ℕ) :
    subsequenceLengthScale t ≤
      (1 / 2 : ℝ) *
        min
          ((7 / 5 : ℝ) ^
              (SoD.ActiveEdge.localOrder (subsequenceEll t) - 1) - 1)
          (SoD.Amplification.errorThreshold /
            decompositionError (subsequenceDegree t)) := by
  have hgrowth := naturalPower_le_amplificationGrowth t
  have herror := naturalPower_le_errorQuotient (subsequenceDegree t)
  have hmin :
      (1 / 100 : ℝ) *
          (2 : ℝ) ^
            (subsequenceDegree t / decompositionDecayDenominator) ≤
        min
          ((7 / 5 : ℝ) ^
              (SoD.ActiveEdge.localOrder (subsequenceEll t) - 1) - 1)
          (SoD.Amplification.errorThreshold /
            decompositionError (subsequenceDegree t)) :=
    le_min hgrowth herror
  unfold subsequenceLengthScale
  nlinarith

/-! ## Concrete dense encoding size -/

namespace LiftedClause

private theorem toParityClauseAux_length (D : LiftedClause N)
    (is : List (Fin N)) :
    (toParityClauseAux D is).length =
      (is.map fun i => if D i = none then 0 else 3).sum := by
  induction is with
  | nil => simp [toParityClauseAux]
  | cons i is ih =>
      cases hDi : D i with
      | none => simp [toParityClauseAux, hDi, ih]
      | some block =>
          simp [toParityClauseAux, hDi, ih, blockFixingClause]
          omega

/-- A lifted width-`w` clause contains exactly `3 * w` parity equations. -/
theorem length_toParityClause_of_mem_liftClause
    {C : Clause N} {D : LiftedClause N} (hD : D ∈ liftClause C) :
    D.toParityClause.length = 3 * C.width := by
  have hsupport : ∀ i, D i = none ↔ C i = none := by
    intro i
    have hcompat := (mem_liftClause_iff C D).mp hD i
    cases hCi : C i <;> cases hDi : D i <;>
      simp [blockOptionCompatible, hCi, hDi] at hcompat ⊢
  rw [toParityClause, toParityClauseAux_length]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [hsupport]
  rw [mul_comm, Clause.width, Clause.support]
  calc
    (∑ x, if C x = none then 0 else 3) =
        ∑ x ∈ Finset.univ.filter (fun x => C x ≠ none), 3 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : C x = none <;> simp [hx]
    _ = (Finset.univ.filter fun x => C x ≠ none).card * 3 := by
      exact Finset.sum_const_nat fun _ _ => rfl

end LiftedClause

/-- The number of clauses in an index lift is at most the number generated
before deduplication. -/
theorem card_indexLift_le_sum_four_pow_width (F : CNF N) :
    (indexLift F).card ≤ ∑ C ∈ F, 4 ^ C.width := by
  classical
  calc
    (indexLift F).card ≤ ∑ C ∈ F, (liftClause C).card :=
      card_indexLift_le_sum_card_liftClause F
    _ = ∑ C ∈ F, 4 ^ C.width := by
      apply Finset.sum_congr rfl
      intro C _
      exact card_liftClause C

theorem card_indexLift_le_card_mul (F : CNF N) :
    (indexLift F).card ≤ F.card * 4 ^ F.width := by
  calc
    (indexLift F).card ≤ ∑ C ∈ F, 4 ^ C.width :=
      card_indexLift_le_sum_four_pow_width F
    _ ≤ ∑ _C ∈ F, 4 ^ F.width := by
      apply Finset.sum_le_sum
      intro C hC
      exact Nat.pow_le_pow_right (by norm_num) (F.clause_width_le_width hC)
    _ = F.card * 4 ^ F.width := by simp

theorem length_indexLift_clause_le
    {F : CNF N} {D : ParityClause (Lemma53.V N)} (hD : D ∈ indexLift F) :
    D.length ≤ 3 * F.width := by
  obtain ⟨C, hCF, L, hLC, rfl⟩ := (mem_indexLift_iff F D).mp hD
  rw [LiftedClause.length_toParityClause_of_mem_liftClause hLC]
  exact Nat.mul_le_mul_left 3 (F.clause_width_le_width hCF)

theorem sum_length_indexLift_le (F : CNF N) :
    (∑ D ∈ indexLift F, D.length) ≤
      (indexLift F).card * (3 * F.width) := by
  calc
    (∑ D ∈ indexLift F, D.length) ≤
        ∑ _D ∈ indexLift F, 3 * F.width := by
      exact Finset.sum_le_sum fun D hD => length_indexLift_clause_le hD
    _ = (indexLift F).card * (3 * F.width) := by simp

namespace DecisionTree

theorem length_allLeafPaths_le_two_pow_depth (T : DecisionTree N α) :
    T.allLeafPaths.length ≤ 2 ^ T.depth := by
  induction T with
  | leaf value => simp [allLeafPaths, depth]
  | query i zeroTree oneTree ihzero ihone =>
      have hzero : 2 ^ zeroTree.depth ≤ 2 ^ max zeroTree.depth oneTree.depth :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
      have hone : 2 ^ oneTree.depth ≤ 2 ^ max zeroTree.depth oneTree.depth :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
      simp only [allLeafPaths, List.length_append, List.length_map, depth]
      calc
        zeroTree.allLeafPaths.length + oneTree.allLeafPaths.length ≤
            2 ^ zeroTree.depth + 2 ^ oneTree.depth := Nat.add_le_add ihzero ihone
        _ ≤ 2 ^ max zeroTree.depth oneTree.depth +
            2 ^ max zeroTree.depth oneTree.depth := Nat.add_le_add hzero hone
        _ = 2 ^ (1 + max zeroTree.depth oneTree.depth) := by
          rw [Nat.add_comm 1, pow_succ]
          omega

theorem card_leafPath_le_two_pow_depth (T : DecisionTree N α) :
    Fintype.card T.LeafPath ≤ 2 ^ T.depth := by
  classical
  have htoFinset : T.allLeafPaths.toFinset = Finset.univ := by
    ext path
    simp [LeafPath.mem_allLeafPaths]
  calc
    Fintype.card T.LeafPath = (Finset.univ : Finset T.LeafPath).card := by simp
    _ = T.allLeafPaths.toFinset.card := by rw [htoFinset]
    _ ≤ T.allLeafPaths.length := List.toFinset_card_le T.allLeafPaths
    _ ≤ 2 ^ T.depth := length_allLeafPaths_le_two_pow_depth T

end DecisionTree

namespace SearchProblem

theorem card_outputClauses_le_leafPath (P : SearchProblem N) (o : P.Output) :
    (P.outputClauses o).card ≤ Fintype.card (P.verifier o).LeafPath := by
  classical
  unfold outputClauses
  calc
    (Finset.univ.biUnion fun leaf : (P.verifier o).LeafPath =>
        if leaf.value = true then
          match leaf.clause with
          | none => ∅
          | some C => {C}
        else ∅).card ≤
        ∑ leaf : (P.verifier o).LeafPath,
          ((if leaf.value = true then
            match leaf.clause with
            | none => (∅ : CNF N)
            | some C => ({C} : CNF N)
          else (∅ : CNF N)) : CNF N).card := Finset.card_biUnion_le
    _ ≤ ∑ _leaf : (P.verifier o).LeafPath, 1 := by
      apply Finset.sum_le_sum
      intro leaf _
      by_cases hvalue : leaf.value = true
      · cases leaf.clause <;> simp [hvalue]
      · simp [hvalue]
    _ = Fintype.card (P.verifier o).LeafPath := by simp

theorem card_toCNF_le_sum_two_pow_depth (P : SearchProblem N) :
    P.toCNF.card ≤ ∑ o : P.Output, 2 ^ (P.verifier o).depth := by
  classical
  unfold toCNF
  calc
    (Finset.univ.biUnion P.outputClauses).card ≤
        ∑ o : P.Output, (P.outputClauses o).card := Finset.card_biUnion_le
    _ ≤ ∑ o : P.Output, Fintype.card (P.verifier o).LeafPath := by
      exact Finset.sum_le_sum fun o _ => P.card_outputClauses_le_leafPath o
    _ ≤ ∑ o : P.Output, 2 ^ (P.verifier o).depth := by
      exact Finset.sum_le_sum fun o _ =>
        DecisionTree.card_leafPath_le_two_pow_depth (P.verifier o)

end SearchProblem

private def encodeSoDOutput {n : ℕ} :
    SoD.Output n → Option (Bool × GridNode n)
  | .inactiveSource => none
  | .activeLast u => some (false, u)
  | .properSink u => some (true, u)

private theorem encodeSoDOutput_injective {n : ℕ} :
    Function.Injective (encodeSoDOutput (n := n)) := by
  intro a b hab
  cases a <;> cases b <;> simp [encodeSoDOutput] at hab ⊢ <;> simp_all

theorem card_soDOutput_le (n : ℕ) :
    Fintype.card (SoD.Output n) ≤ 1 + 2 * n ^ 2 := by
  calc
    Fintype.card (SoD.Output n) ≤
        Fintype.card (Option (Bool × GridNode n)) :=
      Fintype.card_le_of_injective encodeSoDOutput encodeSoDOutput_injective
    _ = 1 + 2 * n ^ 2 := by
      simp [pow_two]
      ring

theorem card_soD_searchCNF_le (ell : ℕ) (hell : 0 < ell) :
    (SoD.Encoding.searchCNF ell hell).card ≤
      (1 + 2 * BinaryPointer.order ell ^ 2) * 2 ^ (2 * ell) := by
  let P := SoD.Encoding.searchProblem ell hell
  have hcard := P.card_toCNF_le_sum_two_pow_depth
  have hdepth :
      (∑ o : P.Output, 2 ^ (P.verifier o).depth) ≤
        ∑ _o : P.Output, 2 ^ (2 * ell) := by
    apply Finset.sum_le_sum
    intro o _
    exact Nat.pow_le_pow_right (by norm_num)
      ((SoD.Encoding.verifier_depth_le hell o))
  calc
    (SoD.Encoding.searchCNF ell hell).card = P.toCNF.card := rfl
    _ ≤ ∑ o : P.Output, 2 ^ (P.verifier o).depth := hcard
    _ ≤ ∑ _o : P.Output, 2 ^ (2 * ell) := hdepth
    _ = Fintype.card P.Output * 2 ^ (2 * ell) := by simp
    _ ≤ (1 + 2 * BinaryPointer.order ell ^ 2) * 2 ^ (2 * ell) := by
      exact Nat.mul_le_mul_right _ (card_soDOutput_le _)

/-- Dense bit size of the parity CNF produced by the index lift. -/
noncomputable def indexLiftBitSize {N : ℕ} (F : CNF N) : ℕ :=
  3 * N + (indexLift F).card +
    ∑ D ∈ indexLift F, D.length * (3 * N + 1)

theorem indexLiftBitSize_le (F : CNF N) :
    indexLiftBitSize F ≤
      3 * N + (F.card * 4 ^ F.width) +
        ((F.card * 4 ^ F.width) * (3 * F.width)) * (3 * N + 1) := by
  let generated := F.card * 4 ^ F.width
  have hcard : (indexLift F).card ≤ generated := card_indexLift_le_card_mul F
  have hsum :
      (∑ D ∈ indexLift F, D.length) ≤ generated * (3 * F.width) :=
    (sum_length_indexLift_le F).trans (Nat.mul_le_mul_right _ hcard)
  unfold indexLiftBitSize
  rw [← Finset.sum_mul]
  exact Nat.add_le_add (Nat.add_le_add_left hcard _) (Nat.mul_le_mul_right _ hsum)

/-! ## Size of the explicit subsequence -/

/-- The ordinary CNF underlying the lifted formula at index `t`. -/
noncomputable def subsequenceBaseFormula (t : ℕ) :
    CNF (SoD.Encoding.variableCount (2 * subsequenceEll t)) :=
  SoD.Preprocess.cleaningFormula (subsequenceEll_pos t)

/-- Dense bit size of the lifted formula at index `t`. -/
noncomputable def subsequenceFormulaSize (t : ℕ) : ℕ :=
  indexLiftBitSize (subsequenceBaseFormula t)

private theorem linear_size_numeric (s : ℕ) (hs : 6 ≤ s) :
    96 * s ≤ 2 ^ (2 * s) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        96 * (s + 1) ≤ 4 * (96 * s) := by nlinarith
        _ ≤ 4 * 2 ^ (2 * s) := Nat.mul_le_mul_left 4 ih
        _ = 2 ^ (2 * (s + 1)) := by
          rw [show 2 * (s + 1) = 2 * s + 2 by ring, pow_add]
          norm_num
          ring

/-- The concrete dense encoding has polynomial size in the chosen degree. -/
theorem subsequenceFormulaSize_le (t : ℕ) :
    subsequenceFormulaSize t ≤ (subsequenceDegree t) ^ 256 := by
  let s := subsequenceShift t
  let A := subsequenceDegree t
  let m := 2 * subsequenceEll t
  let q := BinaryPointer.order m
  let N := SoD.Encoding.variableCount m
  let F := subsequenceBaseFormula t
  have hs : 6 ≤ s := subsequenceShift_six_le t
  have hAdef : A = 2 ^ s := by
    simp [A, s, subsequenceDegree]
  have hA : 64 ≤ A := by
    rw [hAdef]
    calc
      64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hm : m = 16 * s := by
    simp [m, subsequenceEll, s]
    ring
  have hA2 : A ^ 2 = 2 ^ (2 * s) := by
    calc
      A ^ 2 = (2 ^ s) ^ 2 := by rw [hAdef]
      _ = 2 ^ (s * 2) := (pow_mul 2 s 2).symm
      _ = 2 ^ (2 * s) := congrArg (2 ^ ·) (Nat.mul_comm s 2)
  have hlinear := linear_size_numeric s hs
  have hm_le : m ≤ A ^ 2 := by
    rw [hm, hA2]
    omega
  have hwidth_linear : F.width ≤ 32 * s := by
    calc
      F.width ≤ 2 * m := by
        simpa [F, subsequenceBaseFormula] using
          SoD.Preprocess.cleaningFormula_width_le (subsequenceEll_pos t)
      _ = 32 * s := by rw [hm]; ring
  have hwidth : F.width ≤ A ^ 2 := by
    rw [hA2]
    omega
  have hq : q ≤ A ^ 16 := by
    have hpowm : 2 ^ m = A ^ 16 := by
      calc
        2 ^ m = 2 ^ (16 * s) := congrArg (2 ^ ·) hm
        _ = 2 ^ (s * 16) := by rw [Nat.mul_comm 16 s]
        _ = (2 ^ s) ^ 16 := pow_mul 2 s 16
        _ = A ^ 16 := congrArg (· ^ 16) hAdef.symm
    calc
      q ≤ 2 ^ m := by
        dsimp only [q]
        unfold BinaryPointer.order
        omega
      _ = A ^ 16 := hpowm
  have hq2 : q ^ 2 ≤ A ^ 32 := by
    calc
      q ^ 2 ≤ (A ^ 16) ^ 2 := Nat.pow_le_pow_left hq 2
      _ = A ^ 32 := by
        rw [← pow_mul]
  have hN : N ≤ A ^ 34 := by
    calc
      N = q ^ 2 * m := by
        simp [N, SoD.Encoding.variableCount, q, pow_two]
      _ ≤ A ^ 32 * A ^ 2 := Nat.mul_le_mul hq2 hm_le
      _ = A ^ 34 := by rw [← pow_add]
  have hfactor : 1 + 2 * q ^ 2 ≤ A ^ 34 := by
    have hA32pos : 0 < A ^ 32 := pow_pos (by omega) _
    calc
      1 + 2 * q ^ 2 ≤ 3 * A ^ 32 := by omega
      _ ≤ A ^ 2 * A ^ 32 := by
        exact Nat.mul_le_mul_right (A ^ 32) (by nlinarith [hA])
      _ = A ^ 34 := by rw [← pow_add]
  have htwo_m : 2 ^ (2 * m) = A ^ 32 := by
    have hexponent : 2 * m = s * 32 := by
      calc
        2 * m = 2 * (16 * s) := congrArg (2 * ·) hm
        _ = s * 32 := by ring
    calc
      2 ^ (2 * m) = 2 ^ (s * 32) := congrArg (2 ^ ·) hexponent
      _ = (2 ^ s) ^ 32 := pow_mul 2 s 32
      _ = A ^ 32 := congrArg (· ^ 32) hAdef.symm
  have hFcard : F.card ≤ A ^ 66 := by
    have hmpos : 0 < m := by rw [hm]; omega
    calc
      F.card ≤ (1 + 2 * q ^ 2) * 2 ^ (2 * m) := by
        simpa [F, subsequenceBaseFormula, SoD.Preprocess.cleaningFormula, m, q]
          using card_soD_searchCNF_le m hmpos
      _ ≤ A ^ 34 * A ^ 32 := by
        exact Nat.mul_le_mul hfactor (le_of_eq htwo_m)
      _ = A ^ 66 := by rw [← pow_add]
  have hfour_width : 4 ^ F.width ≤ A ^ 64 := by
    calc
      4 ^ F.width ≤ 4 ^ (32 * s) :=
        Nat.pow_le_pow_right (by norm_num) hwidth_linear
      _ = A ^ 64 := by
        have hexponent : 2 * (32 * s) = s * 64 := by ring
        calc
          4 ^ (32 * s) = (2 ^ 2) ^ (32 * s) := by norm_num
          _ = 2 ^ (2 * (32 * s)) := (pow_mul 2 2 (32 * s)).symm
          _ = 2 ^ (s * 64) := congrArg (2 ^ ·) hexponent
          _ = (2 ^ s) ^ 64 := pow_mul 2 s 64
          _ = A ^ 64 := congrArg (· ^ 64) hAdef.symm
  have hgenerated : F.card * 4 ^ F.width ≤ A ^ 130 := by
    calc
      F.card * 4 ^ F.width ≤ A ^ 66 * A ^ 64 :=
        Nat.mul_le_mul hFcard hfour_width
      _ = A ^ 130 := by rw [← pow_add]
  have hthree_width : 3 * F.width ≤ A ^ 3 := by
    calc
      3 * F.width ≤ 3 * A ^ 2 := Nat.mul_le_mul_left 3 hwidth
      _ ≤ A * A ^ 2 := Nat.mul_le_mul_right (A ^ 2) (by omega)
      _ = A ^ 3 := by
        calc
          A * A ^ 2 = A ^ 2 * A := Nat.mul_comm _ _
          _ = A ^ (2 + 1) := (pow_succ A 2).symm
          _ = A ^ 3 := rfl
  have hthree_N : 3 * N + 1 ≤ A ^ 35 := by
    have hA34pos : 0 < A ^ 34 := pow_pos (by omega) _
    calc
      3 * N + 1 ≤ 4 * A ^ 34 := by omega
      _ ≤ A * A ^ 34 := Nat.mul_le_mul_right (A ^ 34) (by omega)
      _ = A ^ 35 := by
        calc
          A * A ^ 34 = A ^ 34 * A := Nat.mul_comm _ _
          _ = A ^ (34 + 1) := (pow_succ A 34).symm
          _ = A ^ 35 := rfl
  have houter : 3 * N ≤ A ^ 35 := by omega
  calc
    subsequenceFormulaSize t = indexLiftBitSize F := rfl
    _ ≤ 3 * N + (F.card * 4 ^ F.width) +
          ((F.card * 4 ^ F.width) * (3 * F.width)) * (3 * N + 1) :=
      indexLiftBitSize_le F
    _ ≤ A ^ 35 + A ^ 130 + (A ^ 130 * A ^ 3) * A ^ 35 := by
      gcongr
    _ = A ^ 35 + A ^ 130 + A ^ 168 := by
      rw [← pow_add, ← pow_add]
    _ ≤ 3 * A ^ 168 := by
      have h35 : A ^ 35 ≤ A ^ 168 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h130 : A ^ 130 ≤ A ^ 168 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    _ ≤ A * A ^ 168 := Nat.mul_le_mul_right (A ^ 168) (by omega)
    _ = A ^ 169 := by
      calc
        A * A ^ 168 = A ^ 168 * A := Nat.mul_comm _ _
        _ = A ^ (168 + 1) := (pow_succ A 168).symm
        _ = A ^ 169 := rfl
    _ ≤ A ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (subsequenceDegree t) ^ 256 := rfl

/-! ## Growth estimates for the family theorem -/

theorem eventually_linear_lt_two_pow (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * n < 2 ^ n := by
  have hlittle :=
    (@isLittleO_coe_const_pow_of_one_lt ℝ _ 2 (by norm_num)).const_mul_left
      (K : ℝ)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < ‖(2 : ℝ) ^ n‖ := by
    exact Filter.Eventually.of_forall fun n =>
      norm_pos_iff.mpr (pow_ne_zero n (by norm_num))
  filter_upwards [hlittle.eventuallyLT_norm_of_eventually_pos hpositive] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
    abs_of_nonneg (pow_nonneg (by norm_num) _)] at hn
  exact_mod_cast hn

theorem formula_power_le_degree_exponent (t d : ℕ) :
    (subsequenceFormulaSize t : ℝ) ^ d ≤
      (2 : ℝ) ^ (256 * d * subsequenceShift t) := by
  calc
    (subsequenceFormulaSize t : ℝ) ^ d ≤
        ((subsequenceDegree t : ℝ) ^ 256) ^ d := by
      gcongr
      exact_mod_cast subsequenceFormulaSize_le t
    _ = (subsequenceDegree t : ℝ) ^ (256 * d) := by
      rw [← pow_mul]
    _ = ((2 : ℝ) ^ subsequenceShift t) ^ (256 * d) := by
      rw [subsequenceDegree]
      norm_cast
    _ = (2 : ℝ) ^ (256 * d * subsequenceShift t) := by
      rw [← pow_mul]
      congr 1
      ring

theorem degree_exponent_lt_lengthScale
    (d t : ℕ)
    (hgrowth :
      (decompositionDecayDenominator * (256 * d + 9)) *
          subsequenceShift t <
        2 ^ subsequenceShift t) :
    (2 : ℝ) ^ (256 * d * subsequenceShift t) <
      subsequenceLengthScale t := by
  let s := subsequenceShift t
  let D := decompositionDecayDenominator
  let A := subsequenceDegree t
  let e := 256 * d * s
  have hs : 1 ≤ s := by
    exact (subsequenceShift_six_le t).trans' (by norm_num)
  have hD : 0 < D := decompositionDecayDenominator_pos
  have hA : A = 2 ^ s := by rfl
  have hproduct : (e + 9) * D ≤ A := by
    calc
      (e + 9) * D = D * (256 * d * s + 9) := by
        simp only [e]
        ring
      _ ≤ D * ((256 * d + 9) * s) := by
        gcongr
        nlinarith
      _ = (D * (256 * d + 9)) * s := by ring
      _ ≤ A := by
        rw [hA]
        exact Nat.le_of_lt hgrowth
  have hquotient : e + 9 ≤ A / D :=
    (Nat.le_div_iff_mul_le hD).2 hproduct
  have hexponent : e + 8 < A / D := by omega
  have htwo :
      (200 : ℝ) * (2 : ℝ) ^ e < (2 : ℝ) ^ (A / D) := by
    calc
      (200 : ℝ) * (2 : ℝ) ^ e <
          (2 : ℝ) ^ 8 * (2 : ℝ) ^ e := by
        gcongr
        norm_num
      _ = (2 : ℝ) ^ (e + 8) := by rw [pow_add]; ring
      _ < (2 : ℝ) ^ (A / D) :=
        pow_lt_pow_right₀ (by norm_num) hexponent
  unfold subsequenceLengthScale
  change (2 : ℝ) ^ e < (1 / 200 : ℝ) * (2 : ℝ) ^ (A / D)
  nlinarith

end Revres
