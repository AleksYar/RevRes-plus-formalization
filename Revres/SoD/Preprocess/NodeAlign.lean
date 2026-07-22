import Revres.Conical.Completion
import Revres.Conical.Representation
import Revres.SoD.Encoding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Node alignment for encoded Sink-of-DAG juntas

Every touched SoD successor record is completed simultaneously.  This preserves the represented
function and multiplies term degree by at most the exact record width.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace Term

/-- A term fixes a node's complete encoded successor pointer. -/
def FixesSuccessor {ell : ℕ} (t : Term (SoD.Encoding.variableCount ell))
    (u : GridNode (BinaryPointer.order ell))
    (pointer : Option (Fin (BinaryPointer.order ell))) : Prop :=
  ∀ b : Fin ell,
    t.val (SoD.Encoding.successorBit u b) =
      some (BinaryPointer.encode pointer b)

namespace FixesSuccessor

theorem nodeBits_subset_support {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)}
    {u : GridNode (BinaryPointer.order ell)}
    {pointer : Option (Fin (BinaryPointer.order ell))}
    (hfix : t.FixesSuccessor u pointer) :
    SoD.Encoding.nodeBits ell u ⊆ t.support := by
  intro i hi
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hi
  exact Term.mem_support.mpr (by simp [hfix b])

theorem unique {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)}
    {u : GridNode (BinaryPointer.order ell)}
    {p q : Option (Fin (BinaryPointer.order ell))}
    (hp : t.FixesSuccessor u p) (hq : t.FixesSuccessor u q) : p = q := by
  rw [← BinaryPointer.decode_encode p, ← BinaryPointer.decode_encode q]
  congr 1
  funext b
  exact Option.some.inj ((hp b).symm.trans (hq b))

theorem matches_decodeInput {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)}
    {u : GridNode (BinaryPointer.order ell)}
    {pointer : Option (Fin (BinaryPointer.order ell))}
    {z : Fin (SoD.Encoding.variableCount ell) → Lemma53.F2}
    (hfix : t.FixesSuccessor u pointer) (hmatch : t.Matches z) :
    (SoD.Encoding.decodeInput z).successor u = pointer := by
  rw [SoD.Encoding.decodeInput_successor, ← BinaryPointer.decode_encode pointer]
  congr 1
  funext b
  exact hmatch _ _ (hfix b)

end FixesSuccessor

/-- A term reads a node when its support contains at least one bit of that node's record. -/
def ReadsNode {ell : ℕ} (t : Term (SoD.Encoding.variableCount ell))
    (u : GridNode (BinaryPointer.order ell)) : Prop :=
  ∃ i ∈ t.support, i ∈ SoD.Encoding.nodeBits ell u

theorem FixesSuccessor.readsNode {ell : ℕ} (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount ell)}
    {u : GridNode (BinaryPointer.order ell)}
    {pointer : Option (Fin (BinaryPointer.order ell))}
    (hfix : t.FixesSuccessor u pointer) : t.ReadsNode u := by
  let b : Fin ell := ⟨0, hell⟩
  exact ⟨SoD.Encoding.successorBit u b,
    hfix.nodeBits_subset_support (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩),
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩

/-- The nodes whose encoded successor records are touched by `t`. -/
noncomputable def readNodes {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    Finset (GridNode (BinaryPointer.order ell)) := by
  classical
  exact t.support.image (SoD.Encoding.nodeOfBit ell)

theorem mem_readNodes_iff {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)}
    {u : GridNode (BinaryPointer.order ell)} :
    u ∈ t.readNodes ↔ t.ReadsNode u := by
  classical
  simp only [readNodes, ReadsNode, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, SoD.Encoding.mem_nodeBits_iff.mpr rfl⟩
  · rintro ⟨i, hi, hib⟩
    exact ⟨i, hi, SoD.Encoding.mem_nodeBits_iff.mp hib⟩

/-- The union of the complete node records touched by `t`. -/
noncomputable def alignmentSupport {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    Finset (Fin (SoD.Encoding.variableCount ell)) := by
  classical
  exact t.readNodes.biUnion (SoD.Encoding.nodeBits ell)

theorem mem_alignmentSupport_iff {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)}
    {i : Fin (SoD.Encoding.variableCount ell)} :
    i ∈ t.alignmentSupport ↔
      ∃ u ∈ t.readNodes, i ∈ SoD.Encoding.nodeBits ell u := by
  classical
  simp [alignmentSupport]

theorem support_subset_alignmentSupport {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    t.support ⊆ t.alignmentSupport := by
  intro i hi
  apply mem_alignmentSupport_iff.mpr
  refine ⟨SoD.Encoding.nodeOfBit ell i, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · exact SoD.Encoding.mem_nodeBits_iff.mpr rfl

/-- Every touched node record is completely fixed by the term. -/
def NodeAligned {ell : ℕ} (t : Term (SoD.Encoding.variableCount ell)) : Prop :=
  ∀ u, t.ReadsNode u → SoD.Encoding.nodeBits ell u ⊆ t.support

theorem NodeAligned.exists_fixesSuccessor_of_readsNode {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)} (haligned : t.NodeAligned)
    {u : GridNode (BinaryPointer.order ell)} (hread : t.ReadsNode u) :
    ∃ pointer, t.FixesSuccessor u pointer := by
  let bits : BinaryPointer.Bits ell := fun b ↦
    (t.val (SoD.Encoding.successorBit u b)).getD 0
  refine ⟨BinaryPointer.decode bits, ?_⟩
  intro b
  rw [BinaryPointer.encode_decode]
  have hbit : SoD.Encoding.successorBit u b ∈ SoD.Encoding.nodeBits ell u :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hsupport := haligned u hread hbit
  have hne := Term.mem_support.mp hsupport
  cases hval : t.val (SoD.Encoding.successorBit u b) with
  | none => exact (hne hval).elim
  | some value => simp [bits, hval]

theorem nodeAligned_iff_alignmentSupport_subset {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)} :
    t.NodeAligned ↔ t.alignmentSupport ⊆ t.support := by
  constructor
  · intro haligned i hi
    obtain ⟨u, hu, hiu⟩ := mem_alignmentSupport_iff.mp hi
    exact haligned u (mem_readNodes_iff.mp hu) hiu
  · intro hsubset u hu i hiu
    exact hsubset (mem_alignmentSupport_iff.mpr
      ⟨u, mem_readNodes_iff.mpr hu, hiu⟩)

theorem card_alignmentSupport {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    t.alignmentSupport.card = t.readNodes.card * ell := by
  classical
  have hpairwise : (t.readNodes : Set (GridNode (BinaryPointer.order ell))).PairwiseDisjoint
      (SoD.Encoding.nodeBits ell) := by
    intro u _hu v _hv huv
    exact SoD.Encoding.nodeBits_disjoint huv
  rw [alignmentSupport, Finset.card_biUnion hpairwise]
  simp

theorem card_readNodes_le_degree {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    t.readNodes.card ≤ t.degree := by
  rw [readNodes, Term.degree]
  exact Finset.card_image_le

theorem card_alignmentSupport_le {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    t.alignmentSupport.card ≤ t.degree * ell := by
  rw [card_alignmentSupport]
  exact Nat.mul_le_mul_right ell t.card_readNodes_le_degree

theorem NodeAligned.degree_eq_readNodes_mul {ell : ℕ}
    {t : Term (SoD.Encoding.variableCount ell)} (haligned : t.NodeAligned) :
    t.degree = t.readNodes.card * ell := by
  have hsupport : t.support = t.alignmentSupport := Finset.Subset.antisymm
    (support_subset_alignmentSupport t)
    (nodeAligned_iff_alignmentSupport_subset.mp haligned)
  rw [Term.degree, hsupport, card_alignmentSupport]

/-- All simultaneous completions of the node records touched by `t`. -/
noncomputable def nodeAlignments {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell)) :
    Finset (Term (SoD.Encoding.variableCount ell)) :=
  t.completeOn t.alignmentSupport

theorem sum_indicator_nodeAlignments {ell : ℕ}
    (t : Term (SoD.Encoding.variableCount ell))
    (z : Fin (SoD.Encoding.variableCount ell) → Lemma53.F2) :
    (∑ u ∈ t.nodeAlignments, u.indicator z) = t.indicator z :=
  t.sum_indicator_completeOn t.alignmentSupport z

theorem support_eq_alignmentSupport_of_mem_nodeAlignments {ell : ℕ}
    {t u : Term (SoD.Encoding.variableCount ell)}
    (hu : u ∈ t.nodeAlignments) :
    u.support = t.alignmentSupport := by
  rw [nodeAlignments] at hu
  rw [support_eq_of_mem_completeOn hu,
    Finset.union_eq_right.mpr (support_subset_alignmentSupport t)]

theorem readNodes_eq_of_mem_nodeAlignments {ell : ℕ}
    {t u : Term (SoD.Encoding.variableCount ell)}
    (hu : u ∈ t.nodeAlignments) :
    u.readNodes = t.readNodes := by
  classical
  have hsupport := support_eq_alignmentSupport_of_mem_nodeAlignments hu
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, hnode⟩ := Finset.mem_image.mp hv
    rw [hsupport] at hi
    obtain ⟨w, hw, hiw⟩ := mem_alignmentSupport_iff.mp hi
    have hiNode : SoD.Encoding.nodeOfBit ell i = w :=
      SoD.Encoding.mem_nodeBits_iff.mp hiw
    exact hnode ▸ hiNode ▸ hw
  · intro hv
    obtain ⟨i, hi, hnode⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hnode⟩
    rw [hsupport]
    exact support_subset_alignmentSupport t hi

theorem nodeAligned_of_mem_nodeAlignments {ell : ℕ}
    {t u : Term (SoD.Encoding.variableCount ell)}
    (hu : u ∈ t.nodeAlignments) :
    u.NodeAligned := by
  rw [nodeAligned_iff_alignmentSupport_subset]
  have hread := readNodes_eq_of_mem_nodeAlignments hu
  have hsupport := support_eq_alignmentSupport_of_mem_nodeAlignments hu
  rw [alignmentSupport, hread, ← alignmentSupport, hsupport]

theorem degree_eq_of_mem_nodeAlignments {ell : ℕ}
    {t u : Term (SoD.Encoding.variableCount ell)}
    (hu : u ∈ t.nodeAlignments) :
    u.degree = t.readNodes.card * ell := by
  rw [Term.degree, support_eq_alignmentSupport_of_mem_nodeAlignments hu,
    card_alignmentSupport]

theorem degree_le_of_mem_nodeAlignments {ell : ℕ}
    {t u : Term (SoD.Encoding.variableCount ell)}
    (hu : u ∈ t.nodeAlignments) :
    u.degree ≤ t.degree * ell := by
  rw [degree_eq_of_mem_nodeAlignments hu]
  exact Nat.mul_le_mul_right ell t.card_readNodes_le_degree

end Term

namespace JuntaRep

variable {ell degree : ℕ}

/-- Every nonzero term in the representation is node-aligned. -/
def NodeAligned (JR : JuntaRep (SoD.Encoding.variableCount ell)) : Prop :=
  ∀ t ∈ JR.support, t.NodeAligned

namespace NodeAligned

theorem zero : NodeAligned (0 : JuntaRep (SoD.Encoding.variableCount ell)) := by
  intro t ht
  simp at ht

theorem single {t : Term (SoD.Encoding.variableCount ell)} {coeff : ℝ}
    (ht : t.NodeAligned) :
    NodeAligned (Finsupp.single t coeff : JuntaRep (SoD.Encoding.variableCount ell)) := by
  classical
  intro u hu
  have hut : u = t := (Finsupp.mem_support_single u t coeff).mp hu |>.1
  simpa [hut] using ht

theorem add {JR KR : JuntaRep (SoD.Encoding.variableCount ell)}
    (hJR : JR.NodeAligned) (hKR : KR.NodeAligned) :
    (JR + KR).NodeAligned := by
  intro t ht
  rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
  · exact hJR t ht
  · exact hKR t ht

theorem finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → JuntaRep (SoD.Encoding.variableCount ell))
    (hf : ∀ i ∈ s, (f i).NodeAligned) :
    (∑ i ∈ s, f i).NodeAligned := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (ell := ell))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end NodeAligned

/-- Expand every supported term into all of its node-aligned completions. -/
noncomputable def nodeAlign (ell : ℕ)
    (JR : JuntaRep (SoD.Encoding.variableCount ell)) :
    JuntaRep (SoD.Encoding.variableCount ell) :=
  ∑ t ∈ JR.support,
    ∑ u ∈ t.nodeAlignments,
      Finsupp.single u (JR t)

theorem eval_nodeAlign_apply
    (JR : JuntaRep (SoD.Encoding.variableCount ell))
    (z : Fin (SoD.Encoding.variableCount ell) → Lemma53.F2) :
    (JR.nodeAlign ell).eval z = JR.eval z := by
  classical
  calc
    (JR.nodeAlign ell).eval z =
        ∑ t ∈ JR.support,
          (∑ u ∈ t.nodeAlignments,
            Finsupp.single u (JR t) : JuntaRep (SoD.Encoding.variableCount ell)).eval z := by
      unfold nodeAlign
      exact JuntaRep.eval_finset_sum JR.support
        (fun t => ∑ u ∈ t.nodeAlignments, Finsupp.single u (JR t)) z
    _ = ∑ t ∈ JR.support,
          ∑ u ∈ t.nodeAlignments, (JR t) * u.indicator z := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [JuntaRep.eval_finset_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [JuntaRep.eval_single]
    _ = ∑ t ∈ JR.support, (JR t) * t.indicator z := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [← Finset.mul_sum, Term.sum_indicator_nodeAlignments]
    _ = JR.eval z := by
      rw [JuntaRep.eval, Finsupp.sum]

theorem eval_nodeAlign
    (JR : JuntaRep (SoD.Encoding.variableCount ell)) :
    (JR.nodeAlign ell).eval = JR.eval := by
  funext z
  exact eval_nodeAlign_apply JR z

theorem nodeAlign_nonnegative
    {JR : JuntaRep (SoD.Encoding.variableCount ell)}
    (hJR : JR.Nonnegative) :
    (JR.nodeAlign ell).Nonnegative := by
  classical
  rw [nodeAlign]
  apply JuntaRep.Nonnegative.finset_sum
  intro t _ht
  apply JuntaRep.Nonnegative.finset_sum
  intro u _hu
  exact JuntaRep.Nonnegative.single (hJR t)

theorem nodeAlign_degreeLE
    {JR : JuntaRep (SoD.Encoding.variableCount ell)}
    (hdegree : JR.DegreeLE degree) :
    (JR.nodeAlign ell).DegreeLE (degree * ell) := by
  classical
  rw [nodeAlign]
  apply JuntaRep.DegreeLE.finset_sum
  intro t ht
  apply JuntaRep.DegreeLE.finset_sum
  intro u hu
  apply JuntaRep.DegreeLE.single
  exact (Term.degree_le_of_mem_nodeAlignments hu).trans
    (Nat.mul_le_mul_right ell (hdegree t ht))

theorem nodeAlign_nodeAligned
    (JR : JuntaRep (SoD.Encoding.variableCount ell)) :
    (JR.nodeAlign ell).NodeAligned := by
  classical
  rw [nodeAlign]
  apply JuntaRep.NodeAligned.finset_sum
  intro t _ht
  apply JuntaRep.NodeAligned.finset_sum
  intro u hu
  exact JuntaRep.NodeAligned.single (Term.nodeAligned_of_mem_nodeAlignments hu)

theorem exists_nodeAligned
    {JR : JuntaRep (SoD.Encoding.variableCount ell)}
    (hnonnegative : JR.Nonnegative)
    (hdegree : JR.DegreeLE degree) :
    ∃ JR' : JuntaRep (SoD.Encoding.variableCount ell),
      JR'.Nonnegative ∧
      JR'.DegreeLE (degree * ell) ∧
      JR'.NodeAligned ∧
      JR'.eval = JR.eval :=
  ⟨JR.nodeAlign ell, nodeAlign_nonnegative hnonnegative,
    nodeAlign_degreeLE hdegree, nodeAlign_nodeAligned JR, eval_nodeAlign JR⟩

end JuntaRep

end Revres
