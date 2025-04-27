import Kura.Operation.Subgraph
import Kura.Walk.Basic

open Set Function List Nat WList
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β}
variable {w : WList α β}
namespace Graph
namespace IsWalk

/-- A subgraph inherits all valid walks -/
lemma le (h : G.IsWalk w) (hle : G ≤ H) : H.IsWalk w := by
  induction h with
  | nil x hx => simp [vx_subset_of_le hle hx]
  | cons' x e w h hw ih => simp_all [h.le hle]

lemma induce (hVd : G.IsWalk w) (hU : w.vxSet ⊆ U) : (G[U]).IsWalk w := by
  induction hVd with
  | nil x => simpa using hU
  | cons' x e w h hw ih =>
    simp_all only [↓cons_vxSet_subset, cons_isWalk_iff, induce_inc₂_iff, true_and, and_true,
      forall_const]
    exact hU.2 (by simp)

lemma of_vxDel (hVd : (G - U).IsWalk w) : G.IsWalk w := hVd.le (vxDel_le G)

lemma vxDel (hVd : G.IsWalk w) (hU : Disjoint w.vxSet U) : (G - U).IsWalk w :=
  hVd.induce <| subset_diff.mpr ⟨hVd.vxSet_subset, hU⟩

lemma restrict (hVd : G.IsWalk w) (hF : w.edgeSet ⊆ F) : (G{F}).IsWalk w := by
  induction hVd with simp_all [insert_subset_iff]

lemma edgeDel (hVd : G.IsWalk w) (hF : Disjoint w.edgeSet F) : (G \ F).IsWalk w :=
  hVd.restrict (by rw [subset_diff]; simp [hF, hVd.edgeSet_subset])

lemma of_edgeDel (h : (G \ F).IsWalk w) : G.IsWalk w := h.le (edgeDel_le G F)

end IsWalk

@[simp]
lemma IsWalk_vxDel : (G - U).IsWalk w ↔ G.IsWalk w ∧ Disjoint w.vxSet U :=
⟨fun h ↦ ⟨h.le (vxDel_le G), fun _V hVw hVU _x hxV ↦ (h.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
  fun ⟨hVd, hU⟩ ↦ hVd.induce (subset_diff.mpr ⟨hVd.vxSet_subset, hU⟩)⟩

@[simp]
lemma IsWalk_restrict : (G{F}).IsWalk w ↔ G.IsWalk w ∧ w.edgeSet ⊆ F := by
  refine ⟨fun h ↦ ⟨h.le (restrict_le G F), fun e he ↦ ?_⟩, fun ⟨hVd, hF⟩ ↦ hVd.restrict hF⟩
  have := h.edgeSet_subset he
  simp only [restrict_E, Set.mem_inter_iff] at this
  exact this.2

@[simp]
lemma IsWalk_edgeDel : (G \ F).IsWalk w ↔ G.IsWalk w ∧ Disjoint w.edgeSet F := by
  rw [edgeDel, IsWalk_restrict, and_congr_right_iff]
  rintro hVd
  simp only [subset_diff, hVd.edgeSet_subset, true_and]

namespace IsWalkFrom

lemma le (h : G.IsWalkFrom S T w) (hle : G ≤ H) : H.IsWalkFrom S T w where
  isWalk := h.isWalk.le hle
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma induce (h : G.IsWalkFrom S T w) (hU : w.vxSet ⊆ U) : G[U].IsWalkFrom S T w where
  isWalk := h.isWalk.induce hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma vxDel (h : G.IsWalkFrom S T w) (hU : Disjoint w.vxSet U) : (G - U).IsWalkFrom S T w where
  isWalk := h.isWalk.vxDel hU
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma of_vxDel (h : (G - U).IsWalkFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk.of_vxDel
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma restrict (h : G.IsWalkFrom S T w) (hF : w.edgeSet ⊆ F) : G{F}.IsWalkFrom S T w where
  isWalk := h.isWalk.restrict hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma edgeDel (h : G.IsWalkFrom S T w) (hF : Disjoint w.edgeSet F) : (G \ F).IsWalkFrom S T w where
  isWalk := h.isWalk.edgeDel hF
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma of_edgeDel (h : (G \ F).IsWalkFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk.of_edgeDel
  first_mem := h.first_mem
  last_mem := h.last_mem

end IsWalkFrom

namespace IsTrail

lemma le (h : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w where
  isWalk := h.isWalk.le hle
  edge_nodup := h.edge_nodup

lemma induce (h : G.IsTrail w) (hU : w.vxSet ⊆ U) : G[U].IsTrail w where
  isWalk := h.isWalk.induce hU
  edge_nodup := h.edge_nodup

lemma vxDel (h : G.IsTrail w) (hU : Disjoint w.vxSet U) : (G - U).IsTrail w where
  isWalk := h.isWalk.vxDel hU
  edge_nodup := h.edge_nodup

lemma of_vxDel (h : (G - U).IsTrail w) : G.IsTrail w where
  isWalk := h.isWalk.of_vxDel
  edge_nodup := h.edge_nodup

lemma restrict (h : G.IsTrail w) (hF : w.edgeSet ⊆ F) : G{F}.IsTrail w where
  isWalk := h.isWalk.restrict hF
  edge_nodup := h.edge_nodup

lemma edgeDel (h : G.IsTrail w) (hF : Disjoint w.edgeSet F) : (G \ F).IsTrail w where
  isWalk := h.isWalk.edgeDel hF
  edge_nodup := h.edge_nodup

lemma of_edgeDel (h : (G \ F).IsTrail w) : G.IsTrail w where
  isWalk := h.isWalk.of_edgeDel
  edge_nodup := h.edge_nodup

end IsTrail

namespace IsPath

lemma le (h : G.IsPath w) (hle : G ≤ H) : H.IsPath w where
  isWalk := h.isWalk.le hle
  nodup := h.nodup

lemma induce (h : G.IsPath w) (hU : w.vxSet ⊆ U) : G[U].IsPath w where
  isWalk := h.isWalk.induce hU
  nodup := h.nodup

lemma vxDel (h : G.IsPath w) (hU : Disjoint w.vxSet U) : (G - U).IsPath w where
  isWalk := h.isWalk.vxDel hU
  nodup := h.nodup

lemma of_vxDel (h : (G - U).IsPath w) : G.IsPath w where
  isWalk := h.isWalk.of_vxDel
  nodup := h.nodup

lemma restrict (h : G.IsPath w) (hF : w.edgeSet ⊆ F) : G{F}.IsPath w where
  isWalk := h.isWalk.restrict hF
  nodup := h.nodup

lemma edgeDel (h : G.IsPath w) (hF : Disjoint w.edgeSet F) : (G \ F).IsPath w where
  isWalk := h.isWalk.edgeDel hF
  nodup := h.nodup

lemma of_edgeDel (h : (G \ F).IsPath w) : G.IsPath w where
  isWalk := h.isWalk.of_edgeDel
  nodup := h.nodup

end IsPath

lemma isPath_vxDel : (G - U).IsPath w ↔ G.IsPath w ∧ Disjoint w.vxSet U :=
  ⟨fun h ↦ ⟨h.of_vxDel, fun _V hVw hVU _x hxV ↦ (h.isWalk.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
    fun ⟨hVp, hU⟩ ↦ hVp.vxDel hU⟩

lemma isPath_edgeDel : (G \ F).IsPath w ↔ G.IsPath w ∧ Disjoint w.edgeSet F := by
  refine ⟨fun h ↦ ⟨h.of_edgeDel, fun _F' hF'w hF'F e heF' ↦ ?_⟩, fun ⟨hVp, hF⟩ ↦ hVp.edgeDel hF⟩
  have := h.isWalk.edgeSet_subset <| hF'w heF'
  simp only [edgeDel_E, mem_diff] at this
  exact this.2 <| hF'F heF'
