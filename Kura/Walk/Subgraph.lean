import Kura.Operation.Subgraph
import Kura.Walk.Defs

open Set Function List Nat Graph.Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β}
namespace Graph
variable {w : Walk α β}

namespace Walk.ValidIn

/-- A subgraph inherits all valid walks -/
lemma le {w : Walk α β} (h : w.ValidIn G) (hle : G ≤ H) : w.ValidIn H := by
  match w with
  | .nil x => exact vx_subset_of_le hle h
  | .cons x e w =>
    obtain ⟨hbtw, hVd⟩ := h
    exact ⟨hbtw.le hle, hVd.le hle⟩

lemma induce (hVd : w.ValidIn G) (hU : w.vxSet ⊆ U) : w.ValidIn (G[U]) := by
  induction w with
  | nil x => simpa using hU
  | cons x e w ih =>
    obtain ⟨hbtw, hVd⟩ := hVd
    obtain ⟨hUx, hUw⟩ := by simpa [cons_vxSet_subset] using hU
    refine ⟨?_, ih hVd hUw⟩
    simp only [induce_inc₂_iff, hbtw, hUx, true_and]
    exact hUw first_mem_vxSet

lemma of_vxDel (hVd : w.ValidIn (G - U)) : w.ValidIn G := hVd.le (vxDel_le G)

lemma vxDel (hVd : w.ValidIn G) (hU : Disjoint w.vxSet U) : w.ValidIn (G - U) :=
  hVd.induce <| subset_diff.mpr ⟨hVd.vxSet_subset, hU⟩

lemma restrict (hVd : w.ValidIn G) (hF : w.edgeSet ⊆ F) : w.ValidIn (G{F}) := by
  induction w with
  | nil x => exact hVd
  | cons x e w ih =>
    obtain ⟨hbtw, hVd⟩ := hVd
    specialize ih hVd (fun e' he' => hF (by simp [he']))
    simp only [cons_validIn, restrict_inc₂, hbtw, true_and, ih, and_true]
    exact hF (by simp [cons_edge])

lemma edgeDel (hVd : w.ValidIn G) (hF : Disjoint w.edgeSet F) : w.ValidIn (G \ F) :=
  hVd.restrict (by rw [subset_diff]; simp [hF, hVd.edgeSet_subset])

lemma of_edgeDel (h : w.ValidIn (G \ F)) : w.ValidIn G := h.le <| edgeDel_le G F

end Walk.ValidIn

@[simp]
lemma validIn_vxDel : w.ValidIn (G - U) ↔ w.ValidIn G ∧ Disjoint w.vxSet U := by
  constructor
  · rintro h
    refine ⟨h.le (vxDel_le G), ?_⟩
    rintro V hVw hVU x hxV
    exact (h.vxSet_subset <| hVw hxV).2 <| hVU hxV
  · rintro ⟨hVd, hU⟩
    exact hVd.induce (subset_diff.mpr ⟨hVd.vxSet_subset, hU⟩)

@[simp]
lemma validIn_restrict : w.ValidIn (G{F}) ↔ w.ValidIn G ∧ w.edgeSet ⊆ F := by
  constructor
  · rintro h
    refine ⟨h.le (restrict_le G F), ?_⟩
    rintro e he
    exact (h.edgeSet_subset he).2
  · rintro ⟨hVd, hF⟩
    exact hVd.restrict hF

@[simp]
lemma validIn_edgeDel : w.ValidIn (G \ F) ↔ w.ValidIn G ∧ Disjoint w.edgeSet F := by
  rw [edgeDel, validIn_restrict, and_congr_right_iff]
  rintro hVd
  simp only [subset_diff, hVd.edgeSet_subset, true_and]

namespace IsWalkFrom

lemma le (h : G.IsWalkFrom S T w) (hle : G ≤ H) : H.IsWalkFrom S T w where
  validIn := h.validIn.le hle
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma induce (h : G.IsWalkFrom S T w) (hU : w.vxSet ⊆ U) : G[U].IsWalkFrom S T w where
  validIn := h.validIn.induce hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma vxDel (h : G.IsWalkFrom S T w) (hU : Disjoint w.vxSet U) : (G - U).IsWalkFrom S T w where
  validIn := h.validIn.vxDel hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma of_vxDel (h : (G - U).IsWalkFrom S T w) : G.IsWalkFrom S T w where
  validIn := h.validIn.of_vxDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma restrict (h : G.IsWalkFrom S T w) (hF : w.edgeSet ⊆ F) : G{F}.IsWalkFrom S T w where
  validIn := h.validIn.restrict hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma edgeDel (h : G.IsWalkFrom S T w) (hF : Disjoint w.edgeSet F) : (G \ F).IsWalkFrom S T w where
  validIn := h.validIn.edgeDel hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma of_edgeDel (h : (G \ F).IsWalkFrom S T w) : G.IsWalkFrom S T w where
  validIn := h.validIn.of_edgeDel
  first_mem := h.first_mem
  last_mem := h.last_mem

end IsWalkFrom

namespace IsTrail

lemma le (h : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w where
  validIn := h.validIn.le hle
  edge_nodup := h.edge_nodup

lemma induce (h : G.IsTrail w) (hU : w.vxSet ⊆ U) : G[U].IsTrail w where
  validIn := h.validIn.induce hU
  edge_nodup := h.edge_nodup

lemma vxDel (h : G.IsTrail w) (hU : Disjoint w.vxSet U) : (G - U).IsTrail w where
  validIn := h.validIn.vxDel hU
  edge_nodup := h.edge_nodup

lemma of_vxDel (h : (G - U).IsTrail w) : G.IsTrail w where
  validIn := h.validIn.of_vxDel
  edge_nodup := h.edge_nodup

lemma restrict (h : G.IsTrail w) (hF : w.edgeSet ⊆ F) : G{F}.IsTrail w where
  validIn := h.validIn.restrict hF
  edge_nodup := h.edge_nodup

lemma edgeDel (h : G.IsTrail w) (hF : Disjoint w.edgeSet F) : (G \ F).IsTrail w where
  validIn := h.validIn.edgeDel hF
  edge_nodup := h.edge_nodup

lemma of_edgeDel (h : (G \ F).IsTrail w) : G.IsTrail w where
  validIn := h.validIn.of_edgeDel
  edge_nodup := h.edge_nodup

end IsTrail

namespace IsPath

lemma le (h : G.IsPath w) (hle : G ≤ H) : H.IsPath w where
  validIn := h.validIn.le hle
  nodup := h.nodup

lemma induce (h : G.IsPath w) (hU : w.vxSet ⊆ U) : G[U].IsPath w where
  validIn := h.validIn.induce hU
  nodup := h.nodup

lemma vxDel (h : G.IsPath w) (hU : Disjoint w.vxSet U) : (G - U).IsPath w where
  validIn := h.validIn.vxDel hU
  nodup := h.nodup

lemma of_vxDel (h : (G - U).IsPath w) : G.IsPath w where
  validIn := h.validIn.of_vxDel
  nodup := h.nodup

lemma restrict (h : G.IsPath w) (hF : w.edgeSet ⊆ F) : G{F}.IsPath w where
  validIn := h.validIn.restrict hF
  nodup := h.nodup

lemma edgeDel (h : G.IsPath w) (hF : Disjoint w.edgeSet F) : (G \ F).IsPath w where
  validIn := h.validIn.edgeDel hF
  nodup := h.nodup

lemma of_edgeDel (h : (G \ F).IsPath w) : G.IsPath w where
  validIn := h.validIn.of_edgeDel
  nodup := h.nodup

end IsPath

lemma isPath_vxDel : (G - U).IsPath w ↔ G.IsPath w ∧ Disjoint w.vxSet U := by
  constructor
  · rintro h
    refine ⟨h.of_vxDel, ?_⟩
    rintro V hVw hVU x hxV
    exact (h.validIn.vxSet_subset <| hVw hxV).2 <| hVU hxV
  · rintro ⟨hVp, hU⟩
    exact hVp.vxDel hU

lemma isPath_edgeDel : (G \ F).IsPath w ↔ G.IsPath w ∧ Disjoint w.edgeSet F := by
  constructor
  · rintro h
    refine ⟨h.of_edgeDel, ?_⟩
    rintro F' hF'w hF'F e heF'
    exact (h.validIn.edgeSet_subset <| hF'w heF').2.2 <| hF'F heF'
  · rintro ⟨hVp, hF⟩
    exact hVp.edgeDel hF
