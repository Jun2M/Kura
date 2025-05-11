import Kura.ST.Separator

namespace Graph
open Set Function List Nat WList
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S S' T T' U V : Set α}
  {F F' R R' : Set β} {w w1 w2 : WList α β}


namespace IsVxSetSeparator

lemma walk_inter (hUsep : G.IsVxSetSeparator S T U) (hWF : G.IsWalkFrom S T w) :
    ∃ x ∈ w, x ∈ U := by
  by_contra! hx
  refine hUsep ?_
  use w.first, hWF.first_mem, w.last, hWF.last_mem
  exact (hWF.validIn.vxDel fun V hV hVU x hxV ↦ hx x (hV hxV) (hVU hxV)).connected

lemma walk_validOn_left (hUsep : G.IsVxSetSeparator S T U) (hVd : V(w)alidIn (G - U))
    (hLeft : ∃ x ∈ w, x ∈ hUsep.leftSet) : V(w)alidIn (G[hUsep.leftSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hLeft
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (hVd.connected_of_mem hxp hy).trans hys

lemma walk_validOn_right (hUsep : G.IsVxSetSeparator S T U) (hVd : V(w)alidIn (G - U))
    (hT : ∃ x ∈ w, x ∈ hUsep.rightSet) : V(w)alidIn (G[hUsep.rightSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hT
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (hVd.connected_of_mem hxp hy).trans hys

lemma path_in_leftHalf_of_finishSep {w : Walk α β} (hP : G.IsPath w)
    (hUsep : G.IsVxSetSeparator S T {w.last}) (hS : w.first ∈ hUsep.leftSet) (hx : x ∈ w.vx) :
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
    · simp [cons_vx_nodup hP.nodup] at hw'
      obtain ⟨y, rfl⟩ := hw'
      right
      simpa using hx
    · apply (path_in_leftHalf_of_finishSep (w := w') hP.cons hUsep · hx)
      simp only [cons_last, cons_first] at hS
      obtain ⟨s, hs, hys⟩ := hS
      use s, hs, Connected.trans ?_ hys
      refine (hP.validIn.1.induce_of_mem hys.mem_left ?_).connected.symm
      refine ⟨hP.validIn.2.vx_mem_of_mem first_mem, hw'⟩

lemma path_validOn_leftHalf_of_finishSep (hUsep : G.IsVxSetSeparator S T {w.last}) (hP : G.IsPath w)
    (hS : w.first ∈ hUsep.leftSet) : V(w)alidIn (G[hUsep.leftSet ∪ {w.last}]) :=
  hP.validIn.induce <| fun _ => path_in_leftHalf_of_finishSep (w := w) hP hUsep hS

instance IsPreorder : IsPreorder (Set α) (IsVxSetSeparator G S) where
  refl A hconn := by
    obtain ⟨x, hxS, hx⟩ := hconn.exists_mem_right
    simp only [vxDel_V, mem_diff, hxS, not_true_eq_false, and_false] at hx
  trans A B C hAB hBC hconn := by
    rw [SetConnected.iff_walk] at hconn
    obtain ⟨w, hwF⟩ := hconn
    obtain ⟨x, hxw, hxB⟩ := hAB.walk_inter (w := w) (hwF.le (induce_le G Set.diff_subset))
    refine hBC ?_
    use w.first, hwF.first_mem, x, hxB, hwF.validIn.connected_first_of_mem hxw

lemma crossingWalk_intersect (hVsep : G.IsVxSetSeparator S T V) [DecidablePred (· ∈ V)]
    (hwF : G.IsWalkFrom (hVsep.leftSet ∪ V) (hVsep.rightSet ∪ V) w) : ∃ x ∈ w.vx, x ∈ V := by
  obtain (hV | ⟨s, hs, hconnStart⟩) := hwF.first_mem.symm
  · use w.first, first_mem
  obtain (hV | ⟨t, ht, hconnFinish⟩) := hwF.last_mem.symm
  · use w.last, last_mem
  by_contra! hw
  have hVd : (G - V).IsWalkFrom _ _ w := hwF.induce fun x hx ↦ ⟨hwF.validIn.vx_mem_of_mem hx, hw x hx⟩
  refine hVsep ?_
  use s, hs, t, ht, hconnStart.symm.trans hVd.validIn.connected |>.trans hconnFinish

lemma crossingWalk_intersect' (hVsep : G.IsVxSetSeparator S T V) [DecidablePred (· ∈ V)]
    (hwF : G.IsWalkFrom (hVsep.rightSet ∪ V) (hVsep.leftSet ∪ V) w) : ∃ x ∈ w.vx, x ∈ V :=
  crossingWalk_intersect hVsep.symm hwF

lemma crossingWalk_endIf_validOn [DecidableEq α] (hVsep : G.IsVxSetSeparator S T V)
    [DecidablePred (· ∈ V)] (hwF : G.IsWalkFrom (hVsep.leftSet ∪ V) (hVsep.rightSet ∪ V) w) :
    (w.endIf (P := (· ∈ V)) (hVsep.crossingWalk_intersect hwF)).ValidIn (G[hVsep.leftSet ∪ V]) := by
  let h := hVsep.crossingWalk_intersect hwF
  refine hwF.validIn.endIf h |>.induce ?_
  rintro x hx
  by_cases hnonempty : ¬ (w.endIf h).Nonempty
  · rw [Nonempty.not_iff] at hnonempty
    obtain ⟨y, hy⟩ := hnonempty
    simp only [hy, nil_vertexSet, mem_singleton_iff] at hx
    subst y
    right
    convert endIf_last h
    simp only [hy, nil_last]
  rw [not_not] at hnonempty
  obtain (rfl | hxV) := mem_dropLast_or_last_of_mem hx |>.symm
  · right
    exact endIf_last h
  · have := dropLast_validIn (hwF.validIn.endIf h)
    have : Walk.ValidIn _ (G - V):= this.induce fun x hx ↦
      ⟨this.vx_mem_of_mem hx, endIf_dropLast_mem_vx h hnonempty hx⟩
    rw [endIf_nonempty_iff] at hnonempty
    have hwfirst := hwF.first_mem
    simp only [mem_union, hnonempty, or_false] at hwfirst
    left
    refine (hVsep.walk_validOn_left this ?_).vx_mem_of_mem hxV
    use w.first, ?_
    convert first_mem using 1
    simp [endIf_nonempty_iff, hnonempty, not_false_eq_true, dropLast_first, endIf_first]

lemma crossingWalk_endIf_validOn' [DecidableEq α] [DecidablePred (· ∈ V)]
    (hVsep : G.IsVxSetSeparator S T V)
    (hwF : G.IsWalkFrom (hVsep.rightSet ∪ V) (hVsep.leftSet ∪ V) w) : (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect' hwF)).ValidIn (G[hVsep.rightSet ∪ V]) :=
  hVsep.symm.crossingWalk_endIf_validOn hwF

lemma leftSetV_iff (h : G.IsVxSetSeparator S T V) (hV : V ⊆ V(G)) (U : Set α) :
    G[h.leftSet ∪ V].IsVxSetSeparator S V U ↔ G.IsVxSetSeparator S V U := by
  classical
  constructor
  · refine fun hUsep hconn ↦ hUsep ?_
    obtain ⟨w, hwF⟩ := hconn.exist_walk
    have hwFG := hwF.le (induce_le G Set.diff_subset)
    have hwFG' : G.IsWalkFrom (h.leftSet ∪ V) (h.rightSet ∪ V) w :=
      hwFG.left_right_subset h.source_subset_leftHalf (by tauto_set)
    have hw' : ∃ x ∈ w.vx, x ∈ V := h.crossingWalk_intersect hwFG'
    have := h.crossingWalk_endIf_validOn hwFG'
    let w' := w.endIf (P := (· ∈ V)) hw'
    use w'.first, (by rw [Walk.endIf_first]; exact hwFG.first_mem), w'.last, Walk.endIf_last hw'
    rw [← vxDel_notation, induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V]
    apply ((hwFG.validIn.endIf hw').induce ?_).connected
    rintro x hx
    exact ⟨this.vx_mem_of_mem hx, (hwF.validIn.vx_mem_of_mem <| endIf_vx_sublist hw' hx).2⟩
    · exact Set.diff_subset
  · rintro hUsep
    refine hUsep.le <| induce_le _ <| Set.union_subset ?_ hV
    exact (leftSet_subset h).trans diff_subset

lemma rightSetV_iff (hVsep : G.IsVxSetSeparator S T V) (hV : V ⊆ V(G)) (U : Set α) :
    G[hVsep.rightSet ∪ V].IsVxSetSeparator V T U ↔ G.IsVxSetSeparator V T U := by
  have := hVsep.symm.leftSetV_iff hV U
  rw [comm (S := V), comm (S := V)]
  convert this using 1

lemma conn_sep_iff_conn_left (hVsep : G.IsVxSetSeparator S T V) (hu : u ∈ hVsep.leftSet)
    (hV : V ⊆ V(G)) :
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
    have hw'VdG : w'.ValidIn G := hwVd.endIf hw'
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

        rw [mem_vertexSet_iff, ← mem_notation, ← List.dropLast_concat_getLast vx_ne_nil,
        List.mem_append, ← dropLast_vx hNonempty, List.mem_singleton, ← w'.last_eq_vx_getLast] at hxw'
        simp only [hxw'Last, or_false] at hxw'
        left
        exact this.vx_mem_of_mem hxw'
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, hy⟩ := hNonempty
      simp only [hy, nil_vertexSet, mem_singleton_iff] at hxw'
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

lemma walk_edges_inter_nonempty (hSep : G.IsEdgeSetSeparator S T F) (hWF : G.IsWalkFrom S T w) :
    (w.edgeSet ∩ F).Nonempty := by
  by_contra! h
  rw [← Set.disjoint_iff_inter_eq_empty] at h
  exact hSep (hWF.edgeDel h |>.setConnected)



end IsEdgeSetSeparator
