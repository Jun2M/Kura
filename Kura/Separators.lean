import Kura..Ignore.SubgraphOld
import Kura.Walk.Operation


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G G' H H' : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}


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

def IsVxSetSeparator (G : Graph α β) (V S T : Set α) : Prop := ¬ (G - V).SetConnected S T

namespace IsVxSetSeparator
variable {U V S S' T T' : Set α} (h : G.IsVxSetSeparator V S T)

def leftSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ s ∈ S, (G - V).Connected v s}

def rightSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ t ∈ T, (G - V).Connected v t}

@[simp] lemma not_isVxSetSeparator : ¬ G.IsVxSetSeparator V S T ↔ (G - V).SetConnected S T := by
  simp [IsVxSetSeparator]

@[simp]
lemma le (h : G'.IsVxSetSeparator V S T) (hle : G ≤ G') : G.IsVxSetSeparator V S T := by
  rintro hconn
  have : G - V ≤ G' - V := vxDel_le_vxDel hle fun ⦃a⦄ a ↦ a
  exact h <| hconn.le this

lemma symm (h : G.IsVxSetSeparator V S T) : G.IsVxSetSeparator V T S := (h ·.symm)

lemma comm : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V T S := ⟨symm, symm⟩

@[simp]
lemma sep_subset (h : G.IsVxSetSeparator U S T) (hUV : U ⊆ V) : G.IsVxSetSeparator V S T :=
  fun hconn ↦ h <| hconn.le <| vxDel_anti G hUV

@[simp]
lemma subset_source (h : G.IsVxSetSeparator V S' T) (hS : S ⊆ S') : G.IsVxSetSeparator V S T :=
  fun hconn ↦ h <| hconn.left_subset hS

@[simp]
lemma subset_target (h : G.IsVxSetSeparator V S T') (hT : T ⊆ T') : G.IsVxSetSeparator V S T :=
  fun hconn ↦ h <| hconn.right_subset hT

@[simp]
lemma empty_iff : G.IsVxSetSeparator ∅ S T ↔ ¬ G.SetConnected S T := by simp [IsVxSetSeparator]

@[simp] lemma empty_source : G.IsVxSetSeparator V ∅ T := by simp [IsVxSetSeparator]

@[simp] lemma empty_target : G.IsVxSetSeparator V S ∅ := by simp [IsVxSetSeparator]

@[simp] lemma univ_sep : G.IsVxSetSeparator univ S T := by simp [IsVxSetSeparator]

@[simp] lemma support_sep : G.IsVxSetSeparator G.V S T := by simp [IsVxSetSeparator]

lemma sep_support : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator (V ∩ G.V) S T := by
  unfold IsVxSetSeparator
  suffices G - V = G - (V ∩ G.V) by rw [this]
  rw [vxDel_eq_vxDel_iff]
  simp

lemma left_support : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) T := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.left_supported, vxDel_V] at hconn ⊢
    exact hconn.left_subset (by tauto_set)
  · rw [SetConnected.left_supported, vxDel_V] at hconn
    exact hconn.left_subset (by tauto_set)

lemma right_support : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T ∩ G.V) := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.right_supported, vxDel_V] at hconn ⊢
    exact hconn.right_subset (by tauto_set)
  · rw [SetConnected.right_supported, vxDel_V] at hconn
    exact hconn.right_subset (by tauto_set)

lemma left_right_support : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) (T ∩ G.V) := by
  rw [left_support, right_support]

lemma left_diff_sep : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S \ V) T := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.left_supported, vxDel_V] at hconn ⊢
    exact hconn.left_subset (by tauto_set)
  · rw [SetConnected.left_supported, vxDel_V] at hconn
    exact hconn.left_subset (by tauto_set)

lemma right_diff_sep : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T \ V) := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.right_supported, vxDel_V] at hconn ⊢
    exact hconn.right_subset (by tauto_set)
  · rw [SetConnected.right_supported, vxDel_V] at hconn
    exact hconn.right_subset (by tauto_set)

lemma source_inter_target_subset (h : G.IsVxSetSeparator V S T) : G.V ∩ S ∩ T ⊆ V := by
  rintro x ⟨⟨hx, hxS⟩, hxT⟩
  by_contra! hxV
  apply h
  use x, hxS, x, hxT, Connected.refl ⟨hx, hxV⟩

@[simp]
lemma vxDel : (G - U).IsVxSetSeparator V S T ↔ G.IsVxSetSeparator (U ∪ V) S T := by
  unfold IsVxSetSeparator
  rw [vxDel_vxDel_eq_vxDel_union]

/- Lemmas about the left and right sets of a separator -/
lemma leftSet_subset (h : G.IsVxSetSeparator V S T) : h.leftSet ⊆ G.V \ V :=
  fun _v ⟨_s, _hs, hconn⟩ ↦ hconn.mem_left

lemma subset_leftSet (h : G.IsVxSetSeparator V S T) (hS : S ⊆ G.V) : S ⊆ h.leftSet ∪ V := by
  rintro s hs
  by_cases h' : s ∈ V
  · exact Or.inr h'
  · left
    use s, hs, Connected.refl ⟨hS hs, h'⟩

lemma rightSet_subset (h : G.IsVxSetSeparator V S T) : h.rightSet ⊆ G.V \ V :=
  fun _v ⟨_t, _ht, hconn⟩ ↦ hconn.mem_left

lemma subset_rightSet (h : G.IsVxSetSeparator V S T) (hT : T ⊆ G.V) : T ⊆ h.rightSet ∪ V := by
  rintro t ht
  by_cases h' : t ∈ V
  · exact Or.inr h'
  · left
    use t, ht, Connected.refl ⟨hT ht, h'⟩

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
    Disjoint h.leftSet h.rightSet := by
  rintro U hUl hUr a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  obtain ⟨t, ht, hconn'⟩ := hUr haU
  apply h
  use s, hs, t, ht, hconn.symm.trans hconn'

@[simp]
lemma leftSet_V_disjoint (h : G.IsVxSetSeparator V S T) : Disjoint h.leftSet V := by
  rintro U hUl hUV a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma rightSet_V_disjoint (h : G.IsVxSetSeparator V S T) : Disjoint h.rightSet V := by
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


lemma walk_inter (hUsep : G.IsVxSetSeparator U S T) (hWF : G.IsWalkFrom S T w) :
    ∃ x ∈ w, x ∈ U := by
  by_contra! hx
  have hVdU := ValidIn.vxDel hWF.validIn fun V hV hVU x hxV ↦ hx x (hV hxV) (hVU hxV)
  exact hUsep w.first hWF.first_mem w.last hWF.last_mem hVdU.connected

lemma walk_validOn_left (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidIn (G - U))
    (hLeft : ∃ x ∈ w, x ∈ hUsep.leftSet) : w.ValidIn (G[hUsep.leftSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hLeft
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (hVd.connected_of_mem hxp hy).trans hys

lemma walk_validOn_right (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidIn (G - U))
    (hT : ∃ x ∈ w, x ∈ hUsep.rightSet) :
    w.ValidIn (G[hUsep.rightSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hT
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (hVd.connected_of_mem hxp hy).trans hys

lemma path_in_leftHalf_of_finishSep {w : Walk α β} (hNodup : w.vx.Nodup) (hVd : w.ValidIn G)
    (hUsep : G.IsVxSetSeparator {w.last} S T) (hS : w.first ∈ hUsep.leftSet) (hx : x ∈ w.vx) :
    x ∈ hUsep.leftSet ∪ {w.last} := by
  obtain (h | h) := em (w.Nonempty) |>.symm
  · right
    rw [Nonempty.not_iff] at h
    obtain ⟨y, hy⟩ := h
    simpa only [hy, nil_last, mem_singleton_iff, nil_vx, mem_cons, not_mem_nil, or_false] using hx
  rw [Nonempty.iff_exists_cons] at h
  obtain ⟨y, e, w', rfl⟩ := h
  simp only [cons_vx, mem_cons] at hx
  obtain (rfl | hx) := hx
  · left
    simpa only [cons_last, cons_first] using hS
  · unfold leftSet
    simp only [cons_last] at hUsep ⊢
    change x ∈ hUsep.leftSet ∪ {w'.last}
    by_cases hw' : w'.first = w'.last
    · simp [cons_vx_nodup hNodup] at hw'
      obtain ⟨y, rfl⟩ := hw'
      right
      simpa using hx
    · apply (path_in_leftHalf_of_finishSep (w := w') (cons_vx_nodup hNodup) hVd.cons hUsep · hx)
      simp only [cons_last, cons_first] at hS
      obtain ⟨s, hs, hys⟩ := hS
      use s, hs, Connected.trans ?_ hys
      refine (hVd.1.induce_of_mem hys.mem_left ?_).connected.symm
      refine ⟨hVd.2.vx_mem_of_mem first_mem, hw'⟩

lemma path_validOn_leftHalf_of_finishSep (hUsep : G.IsVxSetSeparator {w.last} S T) (hNodup : w.vx.Nodup)
    (hVd : w.ValidIn G) (hS : w.first ∈ hUsep.leftSet) :
    w.ValidIn (G[hUsep.leftSet ∪ {w.last}]) :=
  hVd.induce <| fun _ => path_in_leftHalf_of_finishSep (w := w) hNodup hVd hUsep hS

instance IsPreorder : IsPreorder (Set α) (IsVxSetSeparator G · S ·) where
  refl A s hs a ha hconn := by
    have := hconn.mem_right
    simp only [vxDel_V, mem_diff, ha, not_true_eq_false, and_false] at this
  trans A B C hAB hBC s hs c hc hconn := by
    rw [Connected.iff_walk] at hconn
    obtain ⟨p, hpVd, rfl, rfl⟩ := hconn
    obtain ⟨x, hxp, hxB⟩ := hBC.walk_inter (hpVd.le (induce_le G Set.diff_subset)) hs hc
    exact hAB p.first hs x hxB <| hpVd.connected_of_mem first_mem hxp

lemma crossingWalk_intersect (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    (hwVd : w.ValidIn G) (hwfirst : w.first ∈ hVsep.leftSet ∪ V)
    (hwlast : w.last ∈ hVsep.rightSet ∪ V) : ∃ x ∈ w.vx, x ∈ V := by
  rw [mem_union] at hwfirst hwlast
  obtain (hV | ⟨s, hs, hconnStart⟩) := hwfirst.symm <;> clear hwfirst
  · use w.first, first_mem
  obtain (hV | ⟨t, ht, hconnFinish⟩) := hwlast.symm <;> clear hwlast
  · use w.last, last_mem
  by_contra! hw
  have hVd : w.ValidIn (G - V) :=
    hwVd.induce fun x hx ↦ ⟨hwVd.vx_mem_of_mem hx, hw x hx⟩
  exact hVsep s hs t ht <| hconnStart.symm.trans hVd.connected |>.trans hconnFinish

lemma crossingWalk_intersect' (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidIn G) (hwfirst : w.first ∈ hVsep.rightSet ∪ V)
    (hwlast : w.last ∈ hVsep.leftSet ∪ V) : ∃ x ∈ w.vx, x ∈ V :=
  crossingWalk_intersect hVsep.symm hwVd hwfirst hwlast

lemma crossingWalk_endIf_validOn [DecidableEq α] (hVsep : G.IsVxSetSeparator V S T)
    [DecidablePred (· ∈ V)] {w : Walk α β} (hwVd : w.ValidIn G)
    (hwfirst : w.first ∈ hVsep.leftSet ∪ V) (hwlast : w.last ∈ hVsep.rightSet ∪ V) :
    (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect hwVd hwfirst hwlast)).ValidIn (G[hVsep.leftSet ∪ V]) := by
  let h := hVsep.crossingWalk_intersect hwVd hwfirst hwlast
  refine endIf_validIn h hwVd |>.induce ?_
  rintro x hx
  by_cases hnonempty : ¬ (w.endIf h).Nonempty
  · rw [Nonempty.not_iff] at hnonempty
    obtain ⟨y, hy⟩ := hnonempty
    simp only [hy, nil_vxSet, mem_singleton_iff] at hx
    subst y
    right
    convert endIf_last h
    simp only [hy, nil_last]
  rw [not_not] at hnonempty
  obtain (rfl | hxV) := mem_dropLast_or_last_of_mem hx |>.symm
  · right
    exact endIf_last h
  · have := dropLast_validIn (endIf_validIn h hwVd)
    have : Walk.ValidIn _ (G - V):= this.induce fun x hx ↦
      ⟨this.vx_mem_of_mem hx, endIf_dropLast_mem_vx h hnonempty hx⟩
    simp only [endIf_nonempty_iff] at hnonempty
    simp only [mem_union, hnonempty, or_false] at hwfirst
    left
    refine (hVsep.walk_validOn_left this ?_).vx_mem_of_mem hxV
    use w.first, ?_
    convert first_mem using 1
    simp [endIf_nonempty_iff, hnonempty, not_false_eq_true, dropLast_first, endIf_first]

lemma crossingWalk_endIf_validOn' [DecidableEq α] [DecidablePred (· ∈ V)]
    (hVsep : G.IsVxSetSeparator V S T)
    (hwVd : w.ValidIn G) (hwfirst : w.first ∈ hVsep.rightSet ∪ V)
    (hwlast : w.last ∈ hVsep.leftSet ∪ V) : (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect' hwVd hwfirst hwlast)).ValidIn (G[hVsep.rightSet ∪ V]) :=
  hVsep.symm.crossingWalk_endIf_validOn hwVd hwfirst hwlast

lemma leftSetV_iff (h : G.IsVxSetSeparator V S T) (hV : V ⊆ G.V) (U : Set α) :
    G[h.leftSet ∪ V].IsVxSetSeparator U S V ↔ G.IsVxSetSeparator U S V := by
  classical
  constructor
  · rintro hUsep s hs v hv hconn
    rw [Connected.iff_walk] at hconn
    obtain ⟨w, hwVd, rfl, rfl⟩ := hconn
    have hwVdG : w.ValidIn G := hwVd.le (induce_le _ Set.diff_subset)
    have hwfirst : w.first ∈ h.leftSet ∪ V := by
      by_cases hsUv : w.first ∈ V
      · right
        exact hsUv
      · left
        use w.first, hs
        refine Connected.refl ⟨?_, hsUv⟩
        exact Set.diff_subset <| hwVd.vx_mem_of_mem Walk.first_mem
    have hwlast : w.last ∈ h.rightSet ∪ V := Set.mem_union_right h.rightSet hv
    have hw' : ∃ x ∈ w.vx, x ∈ V := h.crossingWalk_intersect hwVdG hwfirst hwlast
    have := h.crossingWalk_endIf_validOn hwVdG hwfirst hwlast
    let w' := w.endIf (P := (· ∈ V)) hw'
    apply hUsep w'.first (by rwa [Walk.endIf_first]) w'.last (Walk.endIf_last hw')
    rw [← vxDel_notation, induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V]
    apply ValidIn.connected
    apply (Walk.endIf_validIn hw' hwVdG).induce
    rintro x hx
    exact ⟨this.vx_mem_of_mem hx, (hwVd.vx_mem_of_mem (Walk.endIf_vx_sublist hw' hx)).2⟩
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
    have hw' : ∃ u ∈ w, (fun x ↦ x ∈ V) u := by use w.last, last_mem
    let w' := w.endIf (P := (· ∈ V)) hw'
    use w'.last, endIf_last hw'
    rw [Connected.iff_walk]
    use w', ?_, endIf_first hw'
    have hw'VdG : w'.ValidIn G := endIf_validIn hw' hwVd
    refine hw'VdG.induce ?_
    rintro x hxw'
    by_cases hNonempty : w'.Nonempty
    · by_cases hxw'Last : x = w'.last
      · subst x
        right
        exact endIf_last hw'
      · have hw'dVdG : w'.dropLast.ValidIn G := dropLast_validIn hw'VdG
        have hw'dvdGV : w'.dropLast.ValidIn (G - V) := by
          refine ValidIn.induce hw'dVdG ?_
          rintro z hz
          exact ⟨hw'dVdG.vx_mem_of_mem hz, endIf_dropLast_mem_vx hw' hNonempty hz⟩
        have : w'.dropLast.ValidIn (G[hVsep.leftSet]) := by
          refine ValidIn.induce hw'dVdG ?_
          rintro y hy
          simp only [leftSet, mem_setOf_eq]
          obtain ⟨s, hs, hsconn⟩ := hu
          use s, hs
          rw [← endIf_first hw', ← dropLast_first hNonempty] at hsconn
          refine Connected.trans ?_ hsconn
          exact ValidIn.connected_of_mem hw'dvdGV hy first_mem

        rw [mem_vxSet_iff, ← mem_notation, ← List.dropLast_concat_getLast vx_ne_nil,
        List.mem_append, ← dropLast_vx hNonempty, List.mem_singleton, ← w'.last_eq_vx_getLast] at hxw'
        simp only [hxw'Last, or_false] at hxw'
        left
        exact this.vx_mem_of_mem hxw'
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, hy⟩ := hNonempty
      simp only [hy, nil_vxSet, mem_singleton_iff] at hxw'
      subst y
      right
      have : w'.last = x := by
        simp only [hy, nil_last]
      exact this ▸ endIf_last hw'
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
