import Kura.Operation.Subgraph
import Kura.Walk.Walk

open Set Function
variable {α β : Type*} {G G₁ G₂ : Graph α β} {u v w x y z : α} {e f g : β}
namespace Graph


@[mk_iff]
structure IsVxSeparator (G : Graph α β) (u v : α) (S : Set α) : Prop where
  not_mem_left : u ∉ S
  not_mem_right : v ∉ S
  not_connected : ¬ (G [G.V \ S]).Connected u v

lemma not_exists_isSeparator_self (hu : u ∈ G.V) : ¬ ∃ S, G.IsVxSeparator u u S :=
  fun ⟨S, hS⟩ ↦ hS.not_connected <| Connected.refl <| by simp [hu, hS.not_mem_left]

-- lemma IsVxSeparator.iff_edgeDel_singleton_isLoop {S : Set α} (he : G.IsLoop e) :
--     G.IsVxSeparator u v S ↔ (G -ᴳ e).IsVxSeparator u v S := by
--   refine ⟨fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩, fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩⟩
--   · by_cases he' : e ∈ G[G.V \ S].E
--     · rw [restrict_V, ← induce_restrict_eq_subgraph]
--       rw [← IsLoop.connected_iff_edgeDel_singleton (e := e)] at hconn
--       convert hconn using 2
--       rw [restrict_eq_restrict_iff]
--       ext e
--       simp +contextual only [induce_E, mem_diff, mem_inter_iff, mem_setOf_eq, mem_singleton_iff,
--         and_self_left, and_congr_right_iff, true_and, implies_true]
--       rwa [IsLoopAt_iff_IsLoopAt_of_edge_mem_le (induce_le G diff_subset) he']
--     · rwa [restrict_V, subgraph_eq_induce]
--       rintro e'
--       simp +contextual only [mem_diff, mem_setOf_eq, mem_singleton_iff]
--       rintro hx
--       sorry
--   · sorry

def IsVxSetSeparator (G : Graph α β) (V S T : Set α) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T, ¬ (G - V).Connected s t

namespace IsVxSetSeparator
variable {U V S S' T T' : Set α} (h : G.IsVxSetSeparator V S T)

def leftSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ s ∈ S, (G - V).Connected v s}

def rightSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ t ∈ T, (G - V).Connected v t}

lemma isVxSetSeparator_iff_inter_vxSet (G : Graph α β) {V S T : Set α} :
    G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) (T ∩ G.V) := sorry

@[simp]
lemma le (h : G₂.IsVxSetSeparator V S T) (hle : G₁ ≤ G₂) : G₁.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t ht (hconn.le (induce_le_induce hle ?_))
  exact Set.diff_subset_diff_left hle.1

lemma symm (h : G.IsVxSetSeparator V S T) : G.IsVxSetSeparator V T S := by
  rintro s hs t ht hconn
  exact h t ht s hs hconn.symm

lemma comm : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V T S := ⟨symm, symm⟩

@[simp]
lemma subset (h : G.IsVxSetSeparator U S T) (hUV : U ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t ht (hconn.le (induce_le_induce (le_refl _) ?_))
  exact diff_subset_diff_right hUV

@[simp]
lemma subset_source (h : G.IsVxSetSeparator V S' T) (hS : S ⊆ S') : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s (hS hs) t ht (hconn.le (le_refl _))

@[simp]
lemma subset_target (h : G.IsVxSetSeparator V S T') (hT : T ⊆ T') : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t (hT ht) (hconn.le (le_refl _))

@[simp]
lemma empty_iff : G.IsVxSetSeparator ∅ S T ↔ (∀ s ∈ S, ∀ t ∈ T, ¬ G.Connected s t) := by
  unfold IsVxSetSeparator
  simp only [vxDel_empty_eq_self]

@[simp]
lemma empty_source : G.IsVxSetSeparator V ∅ T := by
  rintro s hs t ht hconn
  rwa [mem_empty_iff_false] at hs

@[simp]
lemma empty_target : G.IsVxSetSeparator V S ∅ := by
  rintro s hs t ht hconn
  rwa [mem_empty_iff_false] at ht

@[simp]
lemma univ : G.IsVxSetSeparator univ S T := by
  rintro s hs t ht hconn
  simp only [vxDel_V, diff_univ, mem_empty_iff_false, not_false_eq_true,
    not_connected_of_not_mem] at hconn

@[simp]
lemma supp : G.IsVxSetSeparator G.V S T := by
  rintro s hs t ht hconn
  simp only [vxDel_V_eq_bot, instOrderBotGraph, Edgeless.V, mem_empty_iff_false, not_false_eq_true,
    not_connected_of_not_mem] at hconn

@[simp]
lemma source_subset (hSU : S ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  have := hconn.mem_left
  simp only [vxDel_V, mem_diff, hSU hs, not_true_eq_false, and_false] at this

@[simp]
lemma target_subset (hTV : T ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  have := hconn.mem_right
  simp only [vxDel_V, mem_diff, hTV ht, not_true_eq_false, and_false] at this

@[simp]
lemma induce : (G - U).IsVxSetSeparator V S T ↔ G.IsVxSetSeparator (U ∪ V) S T := by
  unfold IsVxSetSeparator
  rw [vxDel_vxDel_eq_vxDel_union]

lemma iff_left_supported : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) T := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s (mem_of_mem_inter_left hs) t ht hconn
  · by_cases h' : s ∈ G.V
    · exact h s (mem_inter hs h') t ht hconn
    · exact h' hconn.mem_left.1

lemma iff_right_supported : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T ∩ G.V) := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s hs t (mem_of_mem_inter_left ht) hconn
  · by_cases h' : t ∈ G.V
    · exact h s hs t (mem_inter ht h') hconn
    · exact h' hconn.mem_right.1

lemma iff_left_diff : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S \ V) T := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s (mem_of_mem_diff hs) t ht hconn
  · exact h s ⟨hs, hconn.mem_left.2⟩ t ht hconn

lemma iff_right_diff : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T \ V) := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s hs t (mem_of_mem_diff ht) hconn
  · exact h s hs t ⟨ht, hconn.mem_right.2⟩ hconn

lemma source_inter_target_subset (h : G.IsVxSetSeparator V S T) : G.V ∩ S ∩ T ⊆ V := by
  rintro x hx
  specialize h x hx.1.2 x hx.2
  simpa only [Connected.refl_iff, vxDel_V, mem_diff, hx.1.1, true_and, not_not] using h

lemma leftSet_subset (h : G.IsVxSetSeparator V S T) : h.leftSet ⊆ G.V \ V :=
  fun _v ⟨_s, _hs, hconn⟩ ↦ hconn.mem_left

lemma subset_leftSet (h : G.IsVxSetSeparator V S T) (hS : S ⊆ G.V) : S ⊆ h.leftSet ∪ V := by
  rintro s hs
  by_cases h' : s ∈ V
  · exact Or.inr h'
  · left
    use s, hs
    exact Connected.refl ⟨hS hs, h'⟩

lemma rightSet_subset (h : G.IsVxSetSeparator V S T) : h.rightSet ⊆ G.V \ V :=
    fun _v ⟨_t, _ht, hconn⟩ ↦ hconn.mem_left

lemma subset_rightSet (h : G.IsVxSetSeparator V S T) (hT : T ⊆ G.V) : T ⊆ h.rightSet ∪ V := by
  rintro t ht
  by_cases h' : t ∈ V
  · exact Or.inr h'
  · left
    use t, ht
    exact Connected.refl ⟨hT ht, h'⟩

@[simp]
lemma symm_leftSet (h : G.IsVxSetSeparator V S T) : h.symm.leftSet = h.rightSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma symm_rightSet (h : G.IsVxSetSeparator V S T) : h.symm.rightSet = h.leftSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma leftSet_rightSet_disjoint (h : G.IsVxSetSeparator V S T) :
    _root_.Disjoint h.leftSet h.rightSet := by
  rintro U hUl hUr a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  obtain ⟨t, ht, hconn'⟩ := hUr haU
  exact h s hs t ht (hconn.symm.trans hconn')

@[simp]
lemma leftSet_V_disjoint (h : G.IsVxSetSeparator V S T) : _root_.Disjoint h.leftSet V := by
  rintro U hUl hUV a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma rightSet_V_disjoint (h : G.IsVxSetSeparator V S T) : _root_.Disjoint h.rightSet V := by
  rintro U hUr hUV a haU
  obtain ⟨t, ht, hconn⟩ := hUr haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma leftSetV_inter_rightSetV (h : G.IsVxSetSeparator V S T) :
    (h.leftSet ∪ V) ∩ (h.rightSet ∪ V) = V := by
  ext a
  simp +contextual only [mem_inter_iff, mem_union, iff_def, and_imp, or_true, and_self,
    implies_true, and_true]
  rintro (hl | hl) (hr | hr) <;> try assumption
  have := h.leftSet_rightSet_disjoint (by simp [hl] : {a} ≤ _) (by simp [hr] : {a} ≤ _)
  simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at this

lemma leftSet_Sep_compl (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.leftSet (h.leftSet ∪ V)ᶜ := by
  rintro a ⟨s, hs, hconnas⟩ b hb hconn
  refine hb ?_
  left
  use s, hs, hconn.symm.trans hconnas

lemma rightSet_Sep_compl (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.rightSet (h.rightSet ∪ V)ᶜ := by
  rintro a ⟨t, ht, hconnat⟩ b hb hconn
  refine hb ?_
  left
  use t, ht, hconn.symm.trans hconnat

lemma compl_Sep_leftSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V (h.leftSet ∪ V)ᶜ h.leftSet := h.leftSet_Sep_compl.symm

lemma compl_Sep_rightSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V (h.rightSet ∪ V)ᶜ h.rightSet := h.rightSet_Sep_compl.symm

lemma leftSet_Sep_rightSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.leftSet h.rightSet := by
  refine h.leftSet_Sep_compl.subset_target ?_
  simp only [compl_union, subset_inter_iff]
  rw [subset_compl_iff_disjoint_left, subset_compl_iff_disjoint_left]
  exact ⟨h.leftSet_rightSet_disjoint, h.rightSet_V_disjoint.symm⟩

lemma mem_of_inc₂_leftSet (hbtw : G.Inc₂ e u v) (hu : u ∈ h.leftSet) :
    v ∈ h.leftSet ∪ V := by
  obtain ⟨s, hs, hconn⟩ := hu
  by_contra! hvV
  simp only [leftSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at hvV
  obtain ⟨hnconn, hvV⟩ := hvV
  exact hnconn s hs
  <| (hbtw.induce_of_mem hconn.mem_left ⟨hbtw.vx_mem_right, hvV⟩).connected.symm.trans hconn

lemma mem_of_inc₂_rightSet (hbtw : G.Inc₂ e u v) (hv : v ∈ h.rightSet) :
    u ∈ h.rightSet ∪ V := by
  obtain ⟨t, ht, hconn⟩ := hv
  by_contra! huV
  simp only [rightSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at huV
  obtain ⟨hnconn, huV⟩ := huV
  refine hnconn t ht <| hbtw.induce_of_mem (⟨hbtw.vx_mem_left, huV⟩ : u ∈ G.V \ V) hconn.mem_left
  |>.connected.trans hconn

/-- Given a set of edges, there is a separator that puts those edges on one side and the rest of
the edges on the other side. -/
def of_edges (G : Graph α β) (U : Set β) :
    G.IsVxSetSeparator {v | (∃ e ∈ U, G.Inc e v) ∧ ∃ e' ∉ U, G.Inc e' v}
    {v | ∃ e ∈ U, G.Inc e v} {v | ∃ e ∉ U, G.Inc e v} := by
  rintro s ⟨e, heU, hse⟩ t ⟨f, hfU, htf⟩ hconn
  sorry


lemma path_inter {p : Path α β} (hUsep : G.IsVxSetSeparator U S T) (hVd : p.val.ValidOn G)
    (hS : p.val.start ∈ S) (hT : p.val.finish ∈ T) : ∃ x ∈ p.val.vx, x ∈ U := by
  by_contra! hx
  have hVdU : p.val.ValidOn (G - U) := by
    refine ValidOn.induce hVd ?_
    rintro x hxp
    exact ⟨hVd.mem_of_mem_vx hxp, hx x hxp⟩
  exact hUsep p.val.start hS p.val.finish hT <| Walk.connected_of_validOn hVdU

lemma walk_validOn_left (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G - U))
    (hLeft : ∃ x ∈ w.vx, x ∈ hUsep.leftSet) : w.ValidOn (G[hUsep.leftSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hLeft
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

lemma walk_validOn_right (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G - U))
    (hT : ∃ x ∈ w.vx, x ∈ hUsep.rightSet) :
    w.ValidOn (G[hUsep.rightSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hT
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

lemma path_in_leftHalf_of_finishSep {w : Walk α β} (hNodup : w.vx.Nodup) (hVd : w.ValidOn G)
    (hUsep : G.IsVxSetSeparator {w.finish} S T) (hS : w.start ∈ hUsep.leftSet) (hx : x ∈ w.vx) :
    x ∈ hUsep.leftSet ∪ {w.finish} := by
  obtain (h | h) := em (w.Nonempty) |>.symm
  · right
    rw [Nonempty.not_iff] at h
    obtain ⟨y, hy⟩ := h
    simpa only [hy, nil_finish, mem_singleton_iff, nil_vx, mem_cons, not_mem_nil, or_false] using hx
  rw [Nonempty.iff_exists_cons] at h
  obtain ⟨y, e, w', rfl⟩ := h
  simp only [cons_vx, mem_cons] at hx
  obtain (rfl | hx) := hx
  · left
    simpa only [cons_finish, cons_start] using hS
  · unfold leftSet
    simp only [cons_finish] at hUsep ⊢
    change x ∈ hUsep.leftSet ∪ {w'.finish}
    by_cases hw' : w'.start = w'.finish
    · simp [cons_vx_nodup hNodup] at hw'
      obtain ⟨y, rfl⟩ := hw'
      right
      simpa using hx
    · apply (path_in_leftHalf_of_finishSep (w := w') (cons_vx_nodup hNodup) hVd.of_cons hUsep · hx)
      simp only [cons_finish, cons_start] at hS
      obtain ⟨s, hs, hys⟩ := hS
      use s, hs, Connected.trans ?_ hys
      refine (hVd.1.induce_of_mem hys.mem_left ?_).connected.symm
      refine ⟨hVd.2.mem_of_mem_vx start_vx_mem, hw'⟩

lemma path_validOn_leftHalf_of_finishSep (hUsep : G.IsVxSetSeparator {p.val.finish} S T)
    (hVd : p.val.ValidOn G) (hS : p.val.start ∈ hUsep.leftSet) :
    p.val.ValidOn (G[hUsep.leftSet ∪ {p.val.finish}]) :=
  hVd.induce <| fun _ => path_in_leftHalf_of_finishSep (w := p.val) p.prop hVd hUsep hS

instance IsPreorder : IsPreorder (Set α) (IsVxSetSeparator G · S ·) where
  refl A s hs a ha hconn := by
    have := hconn.mem_right
    simp only [vxDel_V, mem_diff, ha, not_true_eq_false, and_false] at this
  trans A B C hAB hBC s hs c hc hconn := by
    rw [Connected.iff_path] at hconn
    obtain ⟨p, hpVd, rfl, rfl⟩ := hconn
    obtain ⟨x, hxp, hxB⟩ := hBC.path_inter (hpVd.le (induce_le G Set.diff_subset)) hs hc
    exact hAB p.val.start hs x hxB <| p.val.connected_of_validOn_of_mem hpVd start_vx_mem hxp

lemma crossingWalk_intersect (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.leftSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) : ∃ x ∈ w.vx, x ∈ V := by
  rw [mem_union] at hwstart hwfinish
  obtain (hV | ⟨s, hs, hconnStart⟩) := hwstart.symm <;> clear hwstart
  · use w.start, start_vx_mem
  obtain (hV | ⟨t, ht, hconnFinish⟩) := hwfinish.symm <;> clear hwfinish
  · use w.finish, finish_vx_mem
  by_contra! hw
  have hVd : w.ValidOn (G - V) :=
    hwVd.induce fun x hx ↦ ⟨hwVd.mem_of_mem_vx hx, hw x hx⟩
  exact hVsep s hs t ht <| hconnStart.symm.trans (w.connected_of_validOn hVd) |>.trans hconnFinish

lemma crossingWalk_intersect' (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.rightSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.leftSet ∪ V) : ∃ x ∈ w.vx, x ∈ V :=
  crossingWalk_intersect hVsep.symm hwVd hwstart hwfinish

lemma crossingWalk_endIf_validOn [DecidableEq α] (hVsep : G.IsVxSetSeparator V S T)
    [DecidablePred (· ∈ V)] {w : Walk α β} (hwVd : w.ValidOn G)
    (hwstart : w.start ∈ hVsep.leftSet ∪ V) (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) :
    (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect hwVd hwstart hwfinish)).ValidOn (G[hVsep.leftSet ∪ V]) := by
  let h := hVsep.crossingWalk_intersect hwVd hwstart hwfinish
  refine endIf_validOn h hwVd |>.induce ?_
  rintro x hx
  by_cases hnonempty : ¬ (w.endIf h).Nonempty
  · rw [Nonempty.not_iff] at hnonempty
    obtain ⟨y, hy⟩ := hnonempty
    simp only [hy, nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst y
    right
    convert endIf_finish h
    simp only [hy, nil_finish]
  rw [not_not] at hnonempty
  obtain (rfl | hxV) := mem_dropLast_or_finish_of_mem hx |>.symm
  · right
    exact endIf_finish h
  · have := dropLast_validOn (endIf_validOn h hwVd)
    have : Walk.ValidOn _ (G - V):= this.induce fun x hx ↦
      ⟨this.mem_of_mem_vx hx, endIf_dropLast_mem_vx h hnonempty hx⟩
    simp only [endIf_nonempty_iff] at hnonempty
    simp only [mem_union, hnonempty, or_false] at hwstart
    left
    refine (hVsep.walk_validOn_left this ?_).mem_of_mem_vx hxV
    use w.start, ?_
    convert start_vx_mem using 1
    simp only [endIf_nonempty_iff, hnonempty, not_false_eq_true, dropLast_start, endIf_start]

lemma crossingWalk_endIf_validOn' [DecidableEq α] [DecidablePred (· ∈ V)]
    (hVsep : G.IsVxSetSeparator V S T)
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.rightSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.leftSet ∪ V) : (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect' hwVd hwstart hwfinish)).ValidOn (G[hVsep.rightSet ∪ V]) :=
  hVsep.symm.crossingWalk_endIf_validOn hwVd hwstart hwfinish

lemma leftSetV_iff (h : G.IsVxSetSeparator V S T) (hV : V ⊆ G.V) (U : Set α) :
    G[h.leftSet ∪ V].IsVxSetSeparator U S V ↔ G.IsVxSetSeparator U S V := by
  classical
  constructor
  · rintro hUsep s hs v hv hconn
    rw [Connected.iff_walk] at hconn
    obtain ⟨w, hwVd, rfl, rfl⟩ := hconn
    have hwVdG : w.ValidOn G := hwVd.le (induce_le _ Set.diff_subset)
    have hwstart : w.start ∈ h.leftSet ∪ V := by
      by_cases hsUv : w.start ∈ V
      · right
        exact hsUv
      · left
        use w.start, hs
        refine Connected.refl ⟨?_, hsUv⟩
        exact Set.diff_subset <| hwVd.mem_of_mem_vx (Walk.start_vx_mem)
    have hwfinish : w.finish ∈ h.rightSet ∪ V := Set.mem_union_right h.rightSet hv
    have hw' : ∃ x ∈ w.vx, x ∈ V := h.crossingWalk_intersect hwVdG hwstart hwfinish
    have := h.crossingWalk_endIf_validOn hwVdG hwstart hwfinish
    let w' := w.endIf (P := (· ∈ V)) hw'
    apply hUsep w'.start (by rwa [Walk.endIf_start]) w'.finish (Walk.endIf_finish hw')
    rw [← vxDel_notation, induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V]
    apply w'.connected_of_validOn
    apply (Walk.endIf_validOn hw' hwVdG).induce
    rintro x hx
    exact ⟨this.mem_of_mem_vx hx, (hwVd.mem_of_mem_vx (Walk.endIf_vx_sublist hw' hx)).2⟩
    · exact Set.diff_subset
  · rintro hUsep
    refine hUsep.le <| induce_le _ <| Set.union_subset ?_ hV
    exact (leftSet_subset h).trans diff_subset

lemma rightSetV_iff (hVsep : G.IsVxSetSeparator V S T) (hV : V ⊆ G.V) (U : Set α) :
    G[hVsep.rightSet ∪ V].IsVxSetSeparator U V T ↔ G.IsVxSetSeparator U V T := by
  have := hVsep.symm.leftSetV_iff hV U
  rw [comm (S := V), comm (S := V)]
  convert this using 1

lemma conn_sep_iff_conn_left (hVsep : G.IsVxSetSeparator V S T) (hu : u ∈ hVsep.leftSet)
    (hV : V ⊆ G.V) :
    (∃ v ∈ V, G.Connected u v) ↔ ∃ v ∈ V, G[hVsep.leftSet ∪ V].Connected u v := by
  classical
  constructor
  · rintro ⟨v, hv, hconn⟩
    rw [Connected.iff_walk] at hconn
    obtain ⟨w, hwVd, rfl, rfl⟩ := hconn
    have hw' : ∃ u ∈ w.vx, (fun x ↦ x ∈ V) u := by use w.finish, finish_vx_mem
    let w' := w.endIf (P := (· ∈ V)) hw'
    use w'.finish, Walk.endIf_finish hw'
    rw [Connected.iff_walk]
    use w', ?_, endIf_start hw'
    have hw'VdG : w'.ValidOn G := endIf_validOn hw' hwVd
    refine hw'VdG.induce ?_
    rintro x hxw'
    by_cases hNonempty : w'.Nonempty
    · by_cases hxw'Finish : x = w'.finish
      · subst x
        right
        exact endIf_finish hw'
      · have hw'dVdG : w'.dropLast.ValidOn G := dropLast_validOn hw'VdG
        have hw'dvdGV : w'.dropLast.ValidOn (G - V) := by
          refine ValidOn.induce hw'dVdG ?_
          rintro z hz
          exact ⟨hw'dVdG.mem_of_mem_vx hz, endIf_dropLast_mem_vx hw' hNonempty hz⟩
        have : w'.dropLast.ValidOn (G[hVsep.leftSet]) := by
          refine ValidOn.induce hw'dVdG ?_
          rintro y hy
          simp only [leftSet, mem_setOf_eq]
          obtain ⟨s, hs, hsconn⟩ := hu
          use s, hs
          rw [← endIf_start hw', ← dropLast_start hNonempty] at hsconn
          refine Connected.trans ?_ hsconn
          exact w'.dropLast.connected_of_validOn_of_mem hw'dvdGV hy start_vx_mem

        rw [← List.dropLast_concat_getLast vx_ne_nil, List.mem_append, ← dropLast_vx hNonempty,
        List.mem_singleton, ← w'.finish_eq_vx_getLast] at hxw'
        simp only [hxw'Finish, or_false] at hxw'
        left
        exact this.mem_of_mem_vx hxw'
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, hy⟩ := hNonempty
      simp only [hy, nil_vx, mem_cons, not_mem_nil, or_false] at hxw'
      subst y
      right
      have : w'.finish = x := by
        simp only [hy, nil_finish]
      exact this ▸ endIf_finish hw'
  · rintro ⟨v, hv, hconn⟩
    use v, hv
    refine hconn.le (induce_le G ?_)
    exact union_subset (hVsep.leftSet_subset.trans diff_subset) hV


end IsVxSetSeparator



def IsEdgeSetSeparator (G : Graph α β) (S T : Set α) (F : Set β) :=
  ¬ (G.edgeDel F).SetConnected S T

namespace IsEdgeSetSeparator
variable {G : Graph α β} {S T : Set α} {F F' : Set β}

lemma mono (h : G.IsEdgeSetSeparator S T F) (h_subset : F ⊆ F') :
    G.IsEdgeSetSeparator S T F' := sorry

end IsEdgeSetSeparator
end Graph
