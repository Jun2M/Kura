import Kura.ST.Separator
import Kura.Walk.Lemmas

namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}


namespace IsVxSetSeparator


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


namespace IsEdgeSetSeparator

lemma walk_edges_inter_nonempty (h_sep : G.IsEdgeSetSeparator S T F) {s t : α} (w : Walk G s t)
    (hs : s ∈ S) (ht : t ∈ T) : (Walk.edges w ∩ F).Nonempty := by
  sorry

end IsEdgeSetSeparator
