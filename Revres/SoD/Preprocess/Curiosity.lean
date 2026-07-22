import Revres.SoD.ActiveEdge
import Revres.SoD.Preprocess.NodeAlign
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exit-curiosity for node-aligned Sink-of-DAG juntas

A node-aligned term that fixes a bottom-row pointer to a designated next-macro-row corner is
completed on the full record at that corner.  The simultaneous expansion preserves evaluation and
at most doubles degree.
-/

namespace Revres

open Lemma53
open scoped BigOperators

namespace SoD.Preprocess

/-- A source is a local bottom-row node and the target is a box corner in the next macro-row. -/
def IsDesignatedExit {ell : ℕ} (hell : 0 < ell)
    (source target : GridNode (SoD.ActiveEdge.ambientOrder ell)) : Prop :=
  ∃ Q R u,
    u.IsLastRow ∧
    Q.NextRow R ∧
    source = SoD.ActiveEdge.embedNode hell Q u ∧
    target = SoD.ActiveEdge.embeddedCorner hell R

namespace IsDesignatedExit

theorem source_nextRow_target {ell : ℕ} {hell : 0 < ell}
    {source target : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hexit : IsDesignatedExit hell source target) : source.NextRow target := by
  obtain ⟨Q, R, u, hu, hQR, rfl, rfl⟩ := hexit
  exact SoD.ActiveEdge.embedded_lastRow_nextRow_corner hell hQR hu

theorem target_mem_core {ell : ℕ} {hell : 0 < ell}
    {source target : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hexit : IsDesignatedExit hell source target) :
    ∃ R, target ∈ SoD.ActiveEdge.embeddedSubgrid hell R := by
  obtain ⟨Q, R, u, hu, hQR, hsource, rfl⟩ := hexit
  exact ⟨R, SoD.ActiveEdge.embeddedCorner_mem hell R⟩

theorem target_is_corner {ell : ℕ} {hell : 0 < ell}
    {source target : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hexit : IsDesignatedExit hell source target) :
    ∃ R, target = SoD.ActiveEdge.embeddedCorner hell R := by
  obtain ⟨Q, R, u, hu, hQR, hsource, htarget⟩ := hexit
  exact ⟨R, htarget⟩

end IsDesignatedExit

theorem isDesignatedExit_rightUnique {ell : ℕ} {hell : 0 < ell}
    {source v w : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hv : IsDesignatedExit hell source v)
    (hw : IsDesignatedExit hell source w) (hcolumn : v.column = w.column) : v = w := by
  apply Prod.ext
  · exact GridNode.nextRow_row_unique hv.source_nextRow_target hw.source_nextRow_target
  · exact hcolumn

/-- A designated corner cannot itself be the bottom-row source of another designated exit. -/
theorem designatedExit_target_not_source {ell : ℕ} {hell : 0 < ell}
    {source target : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hexit : IsDesignatedExit hell source target) :
    ¬∃ next, IsDesignatedExit hell target next := by
  rintro ⟨next, hnext⟩
  obtain ⟨Q, R, u, hu, hQR, hsource, htarget⟩ := hexit
  obtain ⟨S, T, v, hv, hST, htarget', hnextTarget⟩ := hnext
  have hembed : SoD.macroEmbed R
      (GridNode.distinguished (BinaryPointer.order_pos hell)) = SoD.macroEmbed S v := by
    apply SoD.ActiveEdge.coreEmbed_injective hell
    exact htarget.symm.trans htarget'
  have hlocal : GridNode.distinguished (BinaryPointer.order_pos hell) = v := by
    simpa using congrArg SoD.localNode hembed
  have horder : SoD.ActiveEdge.localOrder ell = 1 := by
    unfold GridNode.IsLastRow at hv
    rw [← hlocal] at hv
    simpa [GridNode.distinguished] using hv.symm
  have hRlt : R.row.val < SoD.ActiveEdge.localOrder ell := R.row.isLt
  have hRpos : 0 < R.row.val := by
    unfold GridNode.NextRow at hQR
    omega
  omega

end SoD.Preprocess

namespace Term

variable {ell : ℕ}

/-- A read source record that fixes a pointer to a designated exit corner. -/
def TriggersDesignatedExit (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell)))
    (source : GridNode (SoD.ActiveEdge.ambientOrder ell)) : Prop :=
  ∃ target,
    SoD.Preprocess.IsDesignatedExit hell source target ∧
    t.FixesSuccessor source (some target.column)

private noncomputable def selectedExit (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell)))
    (source : GridNode (SoD.ActiveEdge.ambientOrder ell)) :
    GridNode (SoD.ActiveEdge.ambientOrder ell) := by
  classical
  exact if h : t.TriggersDesignatedExit hell source then Classical.choose h
    else GridNode.distinguished (BinaryPointer.order_pos (SoD.ActiveEdge.ambientWidth_pos hell))

private theorem selectedExit_spec (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))}
    {source : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (htrigger : t.TriggersDesignatedExit hell source) :
    SoD.Preprocess.IsDesignatedExit hell source (selectedExit hell t source) ∧
      t.FixesSuccessor source (some (selectedExit hell t source).column) := by
  rw [selectedExit, dif_pos htrigger]
  exact Classical.choose_spec htrigger

private noncomputable def exitSources (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    Finset (GridNode (SoD.ActiveEdge.ambientOrder ell)) := by
  classical
  exact t.readNodes.filter (t.TriggersDesignatedExit hell)

/-- The designated exit corners forced by the successor records fixed by `t`. -/
noncomputable def exitTargets (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    Finset (GridNode (SoD.ActiveEdge.ambientOrder ell)) :=
  (exitSources hell t).image (selectedExit hell t)

theorem mem_exitTargets_iff (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))}
    {target : GridNode (SoD.ActiveEdge.ambientOrder ell)} :
    target ∈ t.exitTargets hell ↔
      ∃ source ∈ t.readNodes,
        SoD.Preprocess.IsDesignatedExit hell source target ∧
        t.FixesSuccessor source (some target.column) := by
  classical
  constructor
  · intro htarget
    obtain ⟨source, hsource, hselected⟩ := Finset.mem_image.mp htarget
    have hsource' : source ∈ t.readNodes.filter (t.TriggersDesignatedExit hell) := by
      simpa [exitSources] using hsource
    have hread : source ∈ t.readNodes := (Finset.mem_filter.mp hsource').1
    have htrigger : t.TriggersDesignatedExit hell source :=
      (Finset.mem_filter.mp hsource').2
    subst target
    exact ⟨source, hread, selectedExit_spec hell htrigger⟩
  · rintro ⟨source, hread, hexit, hfix⟩
    have htrigger : t.TriggersDesignatedExit hell source := ⟨target, hexit, hfix⟩
    apply Finset.mem_image.mpr
    refine ⟨source, ?_, ?_⟩
    · simpa [exitSources] using (Finset.mem_filter.mpr ⟨hread, htrigger⟩)
    have hselected := selectedExit_spec hell htrigger
    have hpointers := hselected.2.unique hfix
    apply SoD.Preprocess.isDesignatedExit_rightUnique hselected.1 hexit
    exact Option.some.inj hpointers

theorem card_exitTargets_le_readNodes (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    (t.exitTargets hell).card ≤ t.readNodes.card := by
  classical
  exact Finset.card_image_le.trans (by
    simpa [exitSources] using
      (Finset.card_filter_le t.readNodes (t.TriggersDesignatedExit hell)))

theorem exitTarget_source (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))}
    {target : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (htarget : target ∈ t.exitTargets hell) :
    ∃ source ∈ t.readNodes,
      SoD.Preprocess.IsDesignatedExit hell source target ∧
      t.FixesSuccessor source (some target.column) :=
  (mem_exitTargets_iff hell).mp htarget

theorem exitTarget_unique (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))}
    {source v w : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hv : SoD.Preprocess.IsDesignatedExit hell source v)
    (hfixv : t.FixesSuccessor source (some v.column))
    (hw : SoD.Preprocess.IsDesignatedExit hell source w)
    (hfixw : t.FixesSuccessor source (some w.column)) : v = w := by
  apply SoD.Preprocess.isDesignatedExit_rightUnique hv hw
  exact Option.some.inj (hfixv.unique hfixw)

/-- All encoded records at the designated exit targets forced by `t`. -/
noncomputable def curiositySupport (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    Finset (Fin (SoD.Encoding.variableCount (2 * ell))) :=
  (t.exitTargets hell).biUnion (SoD.Encoding.nodeBits (2 * ell))

theorem mem_curiositySupport_iff (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))}
    {i : Fin (SoD.Encoding.variableCount (2 * ell))} :
    i ∈ t.curiositySupport hell ↔
      ∃ target ∈ t.exitTargets hell,
        i ∈ SoD.Encoding.nodeBits (2 * ell) target := by
  classical
  simp [curiositySupport]

theorem card_curiositySupport (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    (t.curiositySupport hell).card = (t.exitTargets hell).card * (2 * ell) := by
  classical
  have hpairwise :
      (t.exitTargets hell : Set (GridNode (SoD.ActiveEdge.ambientOrder ell))).PairwiseDisjoint
        (SoD.Encoding.nodeBits (2 * ell)) := by
    intro u _hu v _hv huv
    exact SoD.Encoding.nodeBits_disjoint huv
  rw [curiositySupport, Finset.card_biUnion hpairwise]
  simp

theorem card_curiositySupport_le (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    (t.curiositySupport hell).card ≤ t.readNodes.card * (2 * ell) := by
  rw [card_curiositySupport]
  exact Nat.mul_le_mul_right (2 * ell) (card_exitTargets_le_readNodes hell t)

/-- Every fixed designated exit of a term has its complete target record in support. -/
def ExitCurious (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) : Prop :=
  ∀ source target,
    SoD.Preprocess.IsDesignatedExit hell source target →
    t.FixesSuccessor source (some target.column) →
    SoD.Encoding.nodeBits (2 * ell) target ⊆ t.support

theorem exitCurious_iff_curiositySupport_subset (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))} :
    t.ExitCurious hell ↔ t.curiositySupport hell ⊆ t.support := by
  constructor
  · intro hcurious i hi
    obtain ⟨target, htarget, hitarget⟩ := (mem_curiositySupport_iff hell).mp hi
    obtain ⟨source, hsource, hexit, hfix⟩ := (mem_exitTargets_iff hell).mp htarget
    exact hcurious source target hexit hfix hitarget
  · intro hsupport source target hexit hfix i hi
    apply hsupport
    apply (mem_curiositySupport_iff hell).mpr
    refine ⟨target, ?_, hi⟩
    apply (mem_exitTargets_iff hell).mpr
    exact ⟨source,
      mem_readNodes_iff.mpr (hfix.readsNode (SoD.ActiveEdge.ambientWidth_pos hell)),
      hexit, hfix⟩

theorem card_curiositySupport_le_degree (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))} (haligned : t.NodeAligned) :
    (t.curiositySupport hell).card ≤ t.degree := by
  rw [haligned.degree_eq_readNodes_mul]
  exact card_curiositySupport_le hell t

/-- Complete all records at the designated exits forced by `t`. -/
noncomputable def exitCuriousCompletions (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell))) :
    Finset (Term (SoD.Encoding.variableCount (2 * ell))) :=
  t.completeOn (t.curiositySupport hell)

theorem sum_indicator_exitCuriousCompletions (hell : 0 < ell)
    (t : Term (SoD.Encoding.variableCount (2 * ell)))
    (z : Fin (SoD.Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (∑ u ∈ t.exitCuriousCompletions hell, u.indicator z) = t.indicator z :=
  t.sum_indicator_completeOn (t.curiositySupport hell) z

theorem support_eq_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (hu : u ∈ t.exitCuriousCompletions hell) :
    u.support = t.support ∪ t.curiositySupport hell := by
  exact support_eq_of_mem_completeOn hu

theorem curiositySupport_subset_support_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (hu : u ∈ t.exitCuriousCompletions hell) :
    t.curiositySupport hell ⊆ u.support := by
  intro i hi
  have hunion : i ∈ t.support ∪ t.curiositySupport hell :=
    Finset.mem_union_right _ hi
  rwa [← support_eq_of_mem_exitCuriousCompletions hell hu] at hunion

private theorem readsNode_old_or_exitTarget (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (hu : u ∈ t.exitCuriousCompletions hell)
    {source : GridNode (SoD.ActiveEdge.ambientOrder ell)}
    (hread : u.ReadsNode source) :
    t.ReadsNode source ∨ source ∈ t.exitTargets hell := by
  obtain ⟨i, hiu, hisource⟩ := hread
  rw [support_eq_of_mem_exitCuriousCompletions hell hu] at hiu
  rcases Finset.mem_union.mp hiu with hit | hicuriosity
  · exact Or.inl ⟨i, hit, hisource⟩
  · obtain ⟨target, htarget, hitarget⟩ :=
      (mem_curiositySupport_iff hell).mp hicuriosity
    have hsourceNode := SoD.Encoding.mem_nodeBits_iff.mp hisource
    have htargetNode := SoD.Encoding.mem_nodeBits_iff.mp hitarget
    have hst : source = target := hsourceNode.symm.trans htargetNode
    exact Or.inr (hst.symm ▸ htarget)

private theorem fixesSuccessor_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (hu : u ∈ t.exitCuriousCompletions hell) (haligned : t.NodeAligned)
    {source : GridNode (SoD.ActiveEdge.ambientOrder ell)} (hread : t.ReadsNode source)
    {pointer : Option (Fin (SoD.ActiveEdge.ambientOrder ell))}
    (hfix : u.FixesSuccessor source pointer) : t.FixesSuccessor source pointer := by
  intro b
  have hbit : SoD.Encoding.successorBit source b ∈
      SoD.Encoding.nodeBits (2 * ell) source :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hsupport := haligned source hread hbit
  have hne := Term.mem_support.mp hsupport
  cases hval : t.val (SoD.Encoding.successorBit source b) with
  | none => exact (hne hval).elim
  | some value =>
      have hext : u.val (SoD.Encoding.successorBit source b) = some value := by
        obtain ⟨a, rfl⟩ := mem_completeOn_iff.mp hu
        exact fillOn_extends t (t.curiositySupport hell) a hval
      have hvalue : value = BinaryPointer.encode pointer b :=
        Option.some.inj (hext.symm.trans (hfix b))
      exact congrArg some hvalue

theorem nodeAligned_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (haligned : t.NodeAligned) (hu : u ∈ t.exitCuriousCompletions hell) :
    u.NodeAligned := by
  intro source hread i hi
  obtain ⟨j, hju, hjsource⟩ := hread
  rw [support_eq_of_mem_exitCuriousCompletions hell hu] at hju ⊢
  rcases Finset.mem_union.mp hju with hjt | hjcuriosity
  · exact Finset.mem_union_left _ (haligned source ⟨j, hjt, hjsource⟩ hi)
  · obtain ⟨target, htarget, hjtarget⟩ :=
      (mem_curiositySupport_iff hell).mp hjcuriosity
    have hsourceNode := SoD.Encoding.mem_nodeBits_iff.mp hjsource
    have htargetNode := SoD.Encoding.mem_nodeBits_iff.mp hjtarget
    have hst : source = target := hsourceNode.symm.trans htargetNode
    apply Finset.mem_union_right
    apply (mem_curiositySupport_iff hell).mpr
    exact ⟨target, htarget, hst ▸ hi⟩

private theorem exitTargets_subset_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (haligned : t.NodeAligned) (hu : u ∈ t.exitCuriousCompletions hell) :
    u.exitTargets hell ⊆ t.exitTargets hell := by
  intro target htarget
  obtain ⟨source, hsourceRead, hexit, hfix⟩ := (mem_exitTargets_iff hell).mp htarget
  have hread : u.ReadsNode source :=
    mem_readNodes_iff.mp hsourceRead
  rcases readsNode_old_or_exitTarget hell hu hread with hreadt | hsource
  · have hfixt : t.FixesSuccessor source (some target.column) :=
      fixesSuccessor_of_mem_exitCuriousCompletions hell hu haligned hreadt hfix
    exact (mem_exitTargets_iff hell).mpr
      ⟨source, mem_readNodes_iff.mpr hreadt, hexit, hfixt⟩
  · obtain ⟨previous, hprevious, hpreviousExit, hpreviousFix⟩ :=
      (mem_exitTargets_iff hell).mp hsource
    exact (SoD.Preprocess.designatedExit_target_not_source hpreviousExit ⟨target, hexit⟩).elim

set_option maxHeartbeats 800000 in
-- Unfolding the nested finite trigger/support predicates during this closure proof exceeds the
-- project-wide heartbeat limit; the proof itself only composes the preceding bounded lemmas.
theorem exitCurious_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (haligned : t.NodeAligned) (hu : u ∈ t.exitCuriousCompletions hell) :
    u.ExitCurious hell := by
  apply (exitCurious_iff_curiositySupport_subset (t := u) hell).2
  intro i hi
  obtain ⟨target, htarget, hitarget⟩ := (mem_curiositySupport_iff hell).mp hi
  have htarget' : target ∈ t.exitTargets hell :=
    exitTargets_subset_of_mem_exitCuriousCompletions
      (t := t) (u := u) hell haligned hu htarget
  apply curiositySupport_subset_support_of_mem_exitCuriousCompletions
    (t := t) (u := u) hell hu
  exact (mem_curiositySupport_iff hell).mpr ⟨target, htarget', hitarget⟩

theorem degree_le_of_mem_exitCuriousCompletions (hell : 0 < ell)
    {t u : Term (SoD.Encoding.variableCount (2 * ell))}
    (haligned : t.NodeAligned) (hu : u ∈ t.exitCuriousCompletions hell) :
    u.degree ≤ 2 * t.degree := by
  calc
    u.degree ≤ t.degree + (t.curiositySupport hell).card :=
      degree_le_of_mem_completeOn hu
    _ ≤ t.degree + t.degree :=
      Nat.add_le_add_left (card_curiositySupport_le_degree hell haligned) t.degree
    _ = 2 * t.degree := by omega

end Term

namespace JuntaRep

variable {ell degree : ℕ}

/-- Every nonzero term in the representation is exit-curious. -/
def ExitCurious (hell : 0 < ell)
    (JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))) : Prop :=
  ∀ t ∈ JR.support, t.ExitCurious hell

namespace ExitCurious

theorem zero (hell : 0 < ell) :
    ExitCurious hell (0 : JuntaRep (SoD.Encoding.variableCount (2 * ell))) := by
  intro t ht
  simp at ht

theorem single (hell : 0 < ell)
    {t : Term (SoD.Encoding.variableCount (2 * ell))} {coeff : ℝ}
    (ht : t.ExitCurious hell) :
    ExitCurious hell
      (Finsupp.single t coeff : JuntaRep (SoD.Encoding.variableCount (2 * ell))) := by
  classical
  intro u hu
  have hut : u = t := (Finsupp.mem_support_single u t coeff).mp hu |>.1
  simpa [hut] using ht

theorem add (hell : 0 < ell)
    {JR KR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (hJR : JR.ExitCurious hell) (hKR : KR.ExitCurious hell) :
    (JR + KR).ExitCurious hell := by
  intro t ht
  rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
  · exact hJR t ht
  · exact hKR t ht

theorem finset_sum (hell : 0 < ell) {index : Type*} (s : Finset index)
    (f : index → JuntaRep (SoD.Encoding.variableCount (2 * ell)))
    (hf : ∀ i ∈ s, (f i).ExitCurious hell) :
    (∑ i ∈ s, f i).ExitCurious hell := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero hell
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add hell (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

end ExitCurious

/-- Expand every supported term into all of its exit-curious completions. -/
noncomputable def makeExitCurious (hell : 0 < ell)
    (JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))) :
    JuntaRep (SoD.Encoding.variableCount (2 * ell)) :=
  ∑ t ∈ JR.support,
    ∑ u ∈ t.exitCuriousCompletions hell,
      Finsupp.single u (JR t)

theorem eval_makeExitCurious_apply (hell : 0 < ell)
    (JR : JuntaRep (SoD.Encoding.variableCount (2 * ell)))
    (z : Fin (SoD.Encoding.variableCount (2 * ell)) → Lemma53.F2) :
    (JR.makeExitCurious hell).eval z = JR.eval z := by
  classical
  calc
    (JR.makeExitCurious hell).eval z =
        ∑ t ∈ JR.support,
          (∑ u ∈ t.exitCuriousCompletions hell,
            Finsupp.single u (JR t) :
              JuntaRep (SoD.Encoding.variableCount (2 * ell))).eval z := by
      unfold makeExitCurious
      exact JuntaRep.eval_finset_sum JR.support
        (fun t ↦ ∑ u ∈ t.exitCuriousCompletions hell, Finsupp.single u (JR t)) z
    _ = ∑ t ∈ JR.support,
          ∑ u ∈ t.exitCuriousCompletions hell, (JR t) * u.indicator z := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [JuntaRep.eval_finset_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [JuntaRep.eval_single]
    _ = ∑ t ∈ JR.support, (JR t) * t.indicator z := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [← Finset.mul_sum, Term.sum_indicator_exitCuriousCompletions]
    _ = JR.eval z := by
      rw [JuntaRep.eval, Finsupp.sum]

theorem eval_makeExitCurious (hell : 0 < ell)
    (JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))) :
    (JR.makeExitCurious hell).eval = JR.eval := by
  funext z
  exact eval_makeExitCurious_apply hell JR z

theorem makeExitCurious_nonnegative (hell : 0 < ell)
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (hJR : JR.Nonnegative) : (JR.makeExitCurious hell).Nonnegative := by
  classical
  rw [makeExitCurious]
  apply JuntaRep.Nonnegative.finset_sum
  intro t _ht
  apply JuntaRep.Nonnegative.finset_sum
  intro u _hu
  exact JuntaRep.Nonnegative.single (hJR t)

theorem makeExitCurious_degreeLE (hell : 0 < ell)
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (haligned : JR.NodeAligned) (hdegree : JR.DegreeLE degree) :
    (JR.makeExitCurious hell).DegreeLE (2 * degree) := by
  classical
  rw [makeExitCurious]
  apply JuntaRep.DegreeLE.finset_sum
  intro t ht
  apply JuntaRep.DegreeLE.finset_sum
  intro u hu
  apply JuntaRep.DegreeLE.single
  exact (Term.degree_le_of_mem_exitCuriousCompletions hell (haligned t ht) hu).trans
    (Nat.mul_le_mul_left 2 (hdegree t ht))

theorem makeExitCurious_nodeAligned (hell : 0 < ell)
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (haligned : JR.NodeAligned) : (JR.makeExitCurious hell).NodeAligned := by
  classical
  rw [makeExitCurious]
  apply JuntaRep.NodeAligned.finset_sum
  intro t ht
  apply JuntaRep.NodeAligned.finset_sum
  intro u hu
  exact JuntaRep.NodeAligned.single
    (Term.nodeAligned_of_mem_exitCuriousCompletions hell (haligned t ht) hu)

theorem makeExitCurious_exitCurious (hell : 0 < ell)
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (haligned : JR.NodeAligned) : (JR.makeExitCurious hell).ExitCurious hell := by
  classical
  rw [makeExitCurious]
  apply JuntaRep.ExitCurious.finset_sum hell
  intro t ht
  apply JuntaRep.ExitCurious.finset_sum hell
  intro u hu
  exact JuntaRep.ExitCurious.single hell
    (Term.exitCurious_of_mem_exitCuriousCompletions hell (haligned t ht) hu)

theorem exists_exitCurious (hell : 0 < ell)
    {JR : JuntaRep (SoD.Encoding.variableCount (2 * ell))}
    (hnonnegative : JR.Nonnegative) (hdegree : JR.DegreeLE degree)
    (haligned : JR.NodeAligned) :
    ∃ JR' : JuntaRep (SoD.Encoding.variableCount (2 * ell)),
      JR'.Nonnegative ∧
      JR'.DegreeLE (2 * degree) ∧
      JR'.NodeAligned ∧
      JR'.ExitCurious hell ∧
      JR'.eval = JR.eval :=
  ⟨JR.makeExitCurious hell,
    makeExitCurious_nonnegative hell hnonnegative,
    makeExitCurious_degreeLE hell haligned hdegree,
    makeExitCurious_nodeAligned hell haligned,
    makeExitCurious_exitCurious hell haligned,
    eval_makeExitCurious hell JR⟩

end JuntaRep

end Revres
