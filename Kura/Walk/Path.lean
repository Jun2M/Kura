import Kura.Walk.Basic

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : WList α β}

open WList Set

namespace Graph

/-! ### Trails -/

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : WList α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

/-- `G.IsPath w` means that `w` is a path of `G` with no repeated vertices. -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vx.Nodup

@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
  G.IsPath W, G.IsWalkFrom S T W

lemma IsTrailFrom.isTrail (h : G.IsTrailFrom S T w) : G.IsTrail w where
  isWalk := h.isWalk
  edge_nodup := h.edge_nodup

lemma IsTrailFrom.isWalkFrom (h : G.IsTrailFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.isPath (h : G.IsPathFrom S T w) : G.IsPath w where
  isWalk := h.isWalk
  nodup := h.nodup

lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

-- lemma IsPathFrom.isTrailFrom (h : G.IsPathFrom S T w) : G.IsTrailFrom S T w where
--   isWalk := h.isWalk
--   edge_nodup := h.isPath.isTrail.edge_nodup
--   first_mem := h.first_mem
--   last_mem := h.last_mem

lemma IsWalk.isTrail (hVd : G.IsWalk w) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

lemma IsWalk.isPath (hVd : G.IsWalk w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hVd, hvx⟩

lemma IsWalk.isWalkFrom (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := ⟨hVd, hfirst, hlast⟩

lemma IsWalk.isTrailFrom (hVd : G.IsWalk w) (hedge : w.edge.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsTrailFrom S T w := ⟨⟨hVd, hedge⟩, hfirst, hlast⟩

lemma IsWalk.isPathFrom (hVd : G.IsWalk w) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hVd, hvx⟩, hfirst, hlast⟩

lemma IsTrail.isPath (hT : G.IsTrail w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hT.isWalk, hvx⟩

lemma IsTrail.isTrailFrom (hT : G.IsTrail w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsTrailFrom S T w := ⟨hT, hfirst, hlast⟩

lemma IsTrail.isPathFrom (hT : G.IsTrail w) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hT.isWalk, hvx⟩, hfirst, hlast⟩

lemma IsPath.isPathFrom (hP : G.IsPath w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsPathFrom S T w := ⟨hP, hfirst, hlast⟩

lemma nil_isTrail (hx : x ∈ G.V) : G.IsTrail (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma nil_isPath (hx : x ∈ G.V) : G.IsPath (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma nil_isWalkFrom (hx : x ∈ G.V) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨IsWalk.nil hx, hxS, hxT⟩


@[simp] lemma nil_isWalkFrom_iff : G.IsWalkFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isWalkFrom_iff]

@[simp] lemma nil_isTrail_iff : G.IsTrail (nil x) ↔ x ∈ G.V := by
  simp [isTrail_iff]

@[simp] lemma nil_isPath_iff : G.IsPath (nil x) ↔ x ∈ G.V := by
  simp [isPath_iff]

@[simp] lemma IsPath.first_eq_last (h : G.IsPath w) : w.first = w.last ↔ w.Nil :=
  w.first_eq_last_iff h.nodup

@[simp] lemma cons_isTrail : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge := by
  simp only [isTrail_iff, cons_isWalk_iff, cons_edge, List.nodup_cons]
  tauto

@[simp] lemma cons_isPath : G.IsPath (cons x e w) ↔ G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w := by
  simp only [isPath_iff, cons_isWalk_iff, cons_vx, List.nodup_cons, mem_vx]
  tauto

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isTrailFrom_iff, and_assoc]

@[simp]
lemma cons_isPathFrom : G.IsPathFrom S T (cons x e w) ↔
    G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isPathFrom_iff, and_assoc]

@[simp]
lemma IsTrail.of_cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  rw [cons_isTrail] at h
  exact h.1

@[simp]
lemma IsPath.of_cons (h : G.IsPath (cons x e w)) : G.IsPath w := by
  rw [cons_isPath] at h
  exact h.1

lemma IsPath.exists_cons (h : G.IsPath w) (he : e ∈ w.edge) (hbtw : G.Inc₂ e w.first x) :
    ∃ w' : WList α β, w = cons w.first e w' ∧ G.IsPath w' ∧ w'.first = x := by
  induction w with
  | nil => simp at he
  | cons u f w ih =>
    simp_all only [cons_isPath, cons_edge, List.mem_cons, first_cons, cons.injEq, true_and,
      forall_const]
    obtain (rfl | h') := he
    · use w, ⟨rfl, rfl⟩, h.1, h.2.1.inc₂_iff_eq_right.mp hbtw
    · exact (h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem h' hbtw.inc_left).elim


@[simp]
lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isTrailFrom_iff]

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isPathFrom_iff]

lemma IsPath.isTrail (h : G.IsPath w) : G.IsTrail w where
  isWalk := h.1
  edge_nodup := by
    induction w with
    | nil u => simp
    | cons u e w ih =>
      simp_all only [cons_isPath, cons_edge, List.nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem he h.2.1.inc_left

lemma IsTrail.unique_dInc (h : G.IsTrail w) (he : e ∈ w.edge) :
    ∃! X : α × α, w.DInc e X.fst X.snd := by
  induction w with
  | nil u => simp at he
  | cons u e' w ih =>
    by_cases he' : e' = e
    · subst e' ; clear he ih
      obtain ⟨hT, hbtw, he⟩ := by simpa using h
      have : ¬ w.DInc e u w.first := fun h ↦ he h.edge_mem
      use (u, w.first)
      simp only [dInc_cons_iff, and_self, this, or_false, true_and, Prod.forall, Prod.mk.injEq]
      rintro a b (⟨rfl, rfl⟩ | hdInc)
      · exact ⟨rfl, rfl⟩
      · exact (he hdInc.edge_mem).elim
    · rw [← ne_eq] at he'
      simp only [cons_edge, List.mem_cons, he'.symm, false_or, dInc_cons_iff, he', false_and,
        and_false] at he ⊢
      exact ih h.of_cons he

lemma IsTrail.eq_of_dInc_dInc (h : G.IsTrail w) (hexy : w.DInc e x y) (hexy' : w.DInc e u v) :
    x = u ∧ y = v := by
  obtain ⟨⟨a, b⟩, hdInc, hunique⟩ := h.unique_dInc hexy.edge_mem
  simp only [Prod.forall, Prod.mk.injEq] at hdInc hunique
  obtain ⟨rfl, rfl⟩ := hunique _ _ hexy'
  obtain ⟨rfl, rfl⟩ := hunique _ _ hexy
  exact ⟨rfl, rfl⟩

lemma IsTrail.of_le (h : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w where
  isWalk := h.isWalk.le hle
  edge_nodup := h.edge_nodup

lemma IsTrail.induce (h : G.IsTrail w) (hU : w.vxSet ⊆ U) : G[U].IsTrail w where
  isWalk := h.isWalk.induce hU
  edge_nodup := h.edge_nodup

lemma IsTrail.vxDel (h : G.IsTrail w) (hU : Disjoint w.vxSet U) : (G - U).IsTrail w where
  isWalk := h.isWalk.vxDel hU
  edge_nodup := h.edge_nodup

lemma IsTrail.of_vxDel (h : (G - U).IsTrail w) : G.IsTrail w where
  isWalk := h.isWalk.of_vxDel
  edge_nodup := h.edge_nodup

lemma IsTrail.restrict (h : G.IsTrail w) (hF : w.edgeSet ⊆ F) : G{F}.IsTrail w where
  isWalk := h.isWalk.restrict hF
  edge_nodup := h.edge_nodup

lemma IsTrail.edgeDel (h : G.IsTrail w) (hF : Disjoint w.edgeSet F) : (G \ F).IsTrail w where
  isWalk := h.isWalk.edgeDel hF
  edge_nodup := h.edge_nodup

lemma IsTrail.of_edgeDel (h : (G \ F).IsTrail w) : G.IsTrail w where
  isWalk := h.isWalk.of_edgeDel
  edge_nodup := h.edge_nodup

lemma IsPath.of_le (h : G.IsPath w) (hle : G ≤ H) : H.IsPath w where
  isWalk := h.isWalk.le hle
  nodup := h.nodup

lemma IsPath.induce (h : G.IsPath w) (hU : w.vxSet ⊆ U) : G[U].IsPath w where
  isWalk := h.isWalk.induce hU
  nodup := h.nodup

lemma IsPath.vxDel (h : G.IsPath w) (hU : Disjoint w.vxSet U) : (G - U).IsPath w where
  isWalk := h.isWalk.vxDel hU
  nodup := h.nodup

lemma IsPath.of_vxDel (h : (G - U).IsPath w) : G.IsPath w where
  isWalk := h.isWalk.of_vxDel
  nodup := h.nodup

lemma IsPath.restrict (h : G.IsPath w) (hF : w.edgeSet ⊆ F) : G{F}.IsPath w where
  isWalk := h.isWalk.restrict hF
  nodup := h.nodup

lemma IsPath.edgeDel (h : G.IsPath w) (hF : Disjoint w.edgeSet F) : (G \ F).IsPath w where
  isWalk := h.isWalk.edgeDel hF
  nodup := h.nodup

lemma IsPath.of_edgeDel (h : (G \ F).IsPath w) : G.IsPath w where
  isWalk := h.isWalk.of_edgeDel
  nodup := h.nodup

lemma isPath_vxDel : (G - U).IsPath w ↔ G.IsPath w ∧ Disjoint w.vxSet U :=
  ⟨fun h ↦ ⟨h.of_vxDel, fun _V hVw hVU _x hxV ↦ (h.isWalk.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
    fun ⟨hVp, hU⟩ ↦ hVp.vxDel hU⟩

lemma isPath_edgeDel : (G \ F).IsPath w ↔ G.IsPath w ∧ Disjoint w.edgeSet F := by
  refine ⟨fun h ↦ ⟨h.of_edgeDel, fun _F' hF'w hF'F e heF' ↦ ?_⟩, fun ⟨hVp, hF⟩ ↦ hVp.edgeDel hF⟩
  have := h.isWalk.edgeSet_subset <| hF'w heF'
  simp only [edgeDel_E, Set.mem_diff] at this
  exact this.2 <| hF'F heF'

lemma IsTrailFrom.of_le (h : G.IsTrailFrom S T w) (hle : G ≤ H) : H.IsTrailFrom S T w where
  toIsTrail := h.isTrail.of_le hle
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.induce (h : G.IsTrailFrom S T w) (hU : w.vxSet ⊆ U) : G[U].IsTrailFrom S T w where
  toIsTrail := h.isTrail.induce hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.vxDel (h : G.IsTrailFrom S T w) (hU : Disjoint w.vxSet U) : (G - U).IsTrailFrom S T w where
  toIsTrail := h.isTrail.vxDel hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.of_vxDel (h : (G - U).IsTrailFrom S T w) : G.IsTrailFrom S T w where
  toIsTrail := h.isTrail.of_vxDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.restrict (h : G.IsTrailFrom S T w) (hF : w.edgeSet ⊆ F) : G{F}.IsTrailFrom S T w where
  toIsTrail := h.isTrail.restrict hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.edgeDel (h : G.IsTrailFrom S T w) (hF : Disjoint w.edgeSet F) : (G \ F).IsTrailFrom S T w where
  toIsTrail := h.isTrail.edgeDel hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsTrailFrom.of_edgeDel (h : (G \ F).IsTrailFrom S T w) : G.IsTrailFrom S T w where
  toIsTrail := h.isTrail.of_edgeDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.of_le (h : G.IsPathFrom S T w) (hle : G ≤ H) : H.IsPathFrom S T w where
  toIsPath := h.isPath.of_le hle
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.induce (h : G.IsPathFrom S T w) (hU : w.vxSet ⊆ U) : G[U].IsPathFrom S T w where
  toIsPath := h.isPath.induce hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.vxDel (h : G.IsPathFrom S T w) (hU : Disjoint w.vxSet U) : (G - U).IsPathFrom S T w where
  toIsPath := h.isPath.vxDel hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.of_vxDel (h : (G - U).IsPathFrom S T w) : G.IsPathFrom S T w where
  toIsPath := h.isPath.of_vxDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.restrict (h : G.IsPathFrom S T w) (hF : w.edgeSet ⊆ F) : G{F}.IsPathFrom S T w where
  toIsPath := h.isPath.restrict hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.edgeDel (h : G.IsPathFrom S T w) (hF : Disjoint w.edgeSet F) : (G \ F).IsPathFrom S T w where
  toIsPath := h.isPath.edgeDel hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.of_edgeDel (h : (G \ F).IsPathFrom S T w) : G.IsPathFrom S T w where
  toIsPath := h.isPath.of_edgeDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma Inc₂.walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

lemma IsPath.reverse (hp : G.IsPath w) : G.IsPath w.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

lemma IsPathFrom.reverse (p : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := p.isWalk.reverse
  nodup := by simp [p.nodup]
  first_mem := by simp [p.last_mem]
  last_mem := by simp [p.first_mem]

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse w) ↔ G.IsPath w :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk w) : G.IsPath w.dedup :=
  ⟨h.dedup, w.dedup_vx_nodup⟩



@[simp]
lemma IsPath.dropLast_vxSet {w : WList α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    w.dropLast.vxSet = w.vxSet \ {w.last} := by
  match w with
  | .nil x => simp at hn
  | .cons x e (.nil y) =>
    simp only [dropLast_cons_nil, nil_vxSet, cons_vxSet, pair_comm, last_cons, nil_last,
      mem_singleton_iff, insert_diff_of_mem]
    rw [diff_singleton_eq_self]
    rw [mem_singleton_iff]
    rintro rfl
    simp at hP
  | .cons x e (cons y e' w) =>
    have := dropLast_vxSet (w := cons y e' w)
    simp only [cons_isPath, cons_nonempty, cons_vxSet, last_cons, forall_const, and_imp, first_cons,
      mem_cons_iff, not_or, dropLast_cons_cons] at this hP ⊢
    obtain ⟨⟨hP, h₂', hynin⟩, h₂, hne, hxnin⟩ := hP
    rw [this hP h₂' hynin, ← insert_diff_of_not_mem, insert_comm]
    simp only [mem_singleton_iff]
    rintro rfl
    simp only [last_mem, not_true_eq_false] at hxnin

@[simp]
lemma IsPath.last_not_mem_dropLast (hP : G.IsPath w) (hn : w.Nonempty) :
    w.last ∉ w.dropLast := by
  rintro h
  rw [← mem_vxSet_iff, hP.dropLast_vxSet hn] at h
  simp at h


section Connected

lemma connected_iff_exists_path : G.Connected x y ↔ ∃ w, G.IsPath w ∧ w.first = x ∧ w.last = y := by
  classical
  rw [connected_iff_exists_walk]
  exact ⟨fun ⟨w, hVd, hx, hy⟩ ↦ ⟨w.dedup, hVd.dedup_isPath, hx ▸ w.dedup_first, hy ▸ w.dedup_last⟩,
    fun ⟨w, hVd, hx, hy⟩ ↦ ⟨w, hVd.isWalk, hx, hy⟩⟩

lemma setConnected_iff_exists_pathFrom : G.SetConnected S T ↔ ∃ w, G.IsPathFrom S T w ∧
    w.first ∈ S ∧ w.last ∈ T := by
  simp_rw [SetConnected, connected_iff_exists_path]
  exact ⟨fun ⟨s, hsS, t, htT, w, hVd, hs, ht⟩ ↦ ⟨w, hVd.isPathFrom (hs ▸ hsS) (ht ▸ htT), hs ▸ hsS,
    ht ▸ htT⟩, fun ⟨w, hVd, hx, hy⟩ ↦ ⟨w.first, hx, w.last, hy, w, hVd.isPath, rfl, rfl⟩⟩



end Connected

end Graph
