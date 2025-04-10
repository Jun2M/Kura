import Kura.Basic
import Kura.Dep.SetPartition

open Set Function
variable {α α' β : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


def ConnectedPartition (G : Graph α β) : Partition G.V :=
  Partition.ofRel' (G.Connected) (by
    ext v
    simp only [Connected.refl_iff, setOf_mem_eq])

-- namespace ConnectedPartition

-- noncomputable def rep (x : α) (hx : x ∈ G.V) : α :=
--   G.ConnectedPartition.rep (G.ConnectedPartition.partOf_mem hx)

-- @[simp]
-- lemma rep_mem (hx : x ∈ G.V) : rep x hx ∈ G.V :=
--   Partition.rep_mem' (G.ConnectedPartition.partOf_mem hx)

-- @[simp]
-- lemma rep_connected (hx : x ∈ G.V) :
--     G.Connected (rep x hx) x := by
--   rw [Connected.comm]
--   convert G.ConnectedPartition.rep_rel (G.ConnectedPartition.partOf_mem hx) (G.ConnectedPartition.mem_partOf hx)
--   rw [eq_comm]
--   exact Partition.rel_ofRel'_eq (G.Connected) (by simp only [Connected.refl_iff, setOf_mem_eq])

-- @[simp]
-- lemma req_eq_iff_connected (hx : x ∈ G.V) (hy : y ∈ G.V) :
--     rep x hx = rep y hy ↔ G.Connected x y := by
--   constructor <;> rintro h
--   · exact (rep_connected hx).symm.trans (h ▸ rep_connected hy)
--   · rw [Partition.rel_iff_eqv_class_eq_left (Connected.refl hx)] at h
--     simp [rep]
--     congr
--     refine Partition.eq_partOf_of_mem (G.ConnectedPartition.partOf_mem hx) ?_
--     simp only [Partition.partOf, mem_sUnion, mem_setOf_eq]
--     use {z | G.Connected y z}, ⟨?_, ?_⟩, Connected.refl hy
--     · rw [ConnectedPartition, Partition.mem_ofRel'_iff]
--       use x, hx
--       rw [h]
--     · rw [← h]
--       exact Connected.refl hx

-- lemma rep_idem (hx : x ∈ G.V) :
--     rep (rep x hx) (rep_mem hx) = rep x hx := by
--   simp only [rep, Partition.partOf_rep]

-- end ConnectedPartition


lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
    (G.incFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
  classical
  simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
    Finsupp.single_apply, and_comm, ← incFun_ne_zero]

/-- Maps are easy too -/
noncomputable def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  incFun e := (G.incFun e).mapDomain f
  sum_eq e he := by rwa [Finsupp.sum_mapDomain_index (by simp) (by simp), G.sum_eq]
  vertex_support e v := by
    classical
    simp only [ne_eq, vxMap_aux, Set.mem_image, forall_exists_index, and_imp]
    exact fun x hxv h ↦ ⟨x, h.vx_mem, hxv⟩
  edge_support e v := by
    classical
    simp only [ne_eq, vxMap_aux, forall_exists_index, and_imp]
    exact fun _ _ ↦ Inc.edge_mem

variable {α' : Type*} {φ : α → α'}

@[simp]
lemma vxMap.V : (G.vxMap φ).V = φ '' G.V := rfl

@[simp]
lemma vxMap.E : (G.vxMap φ).E = G.E := rfl

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc_iff (G : Graph α β) (f : α → α') (x : α') (e : β) :
    (G.vxMap f).Inc e x ↔ ∃ v, f v = x ∧ G.Inc e v := by
  rw [← incFun_ne_zero, ← vxMap_aux]
  rfl

@[simp]
lemma vxMap_toMultiset_eq_map_toMultiset (G : Graph α β) (f : α → α') (e : β) :
    (G.vxMap f).toMultiset e = Multiset.map f (G.toMultiset e) := by
  simp only [vxMap, toMultiset, Finsupp.toMultiset_map]

lemma IsBetween.vxMap_of_isBetween {x y : α} (hBtw : G.IsBetween e x y) (φ : α → α') :
    (G.vxMap φ).IsBetween e (φ x) (φ y) := by
  unfold IsBetween at hBtw ⊢
  simp only [Multiset.insert_eq_cons, vxMap_toMultiset_eq_map_toMultiset, ← hBtw, Multiset.map_cons,
    Multiset.map_singleton]

@[simp]
lemma vxMap.IsBetween {x y : α'} : (G.vxMap φ).IsBetween e x y ↔
    ∃ x', φ x' = x ∧ ∃ y', φ y' = y ∧ G.IsBetween e x' y' := by
  constructor
  · rintro hBtw
    obtain he : e ∈ G.E := hBtw.edge_mem
    obtain ⟨x', y', hbtw⟩ := exist_IsBetween_of_mem he
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (hbtw.vxMap_of_isBetween φ).eq_or_eq_of_IsBetween hBtw
    · use x', rfl, y'
    · use y', rfl, x', rfl
      exact hbtw.symm
  · rintro ⟨x', rfl, y', rfl, hbtw⟩
    exact hbtw.vxMap_of_isBetween φ


-- def edgePreimg {β' : Type*} (G : Graph α β) (σ : β' → β) : Graph α β' where
--   V := G.V
--   E := σ ⁻¹' G.E
--   Inc v e := G.Inc v (σ e)
--   vx_mem_of_inc v e hinc := G.vx_mem_of_inc hinc
--   edge_mem_of_inc v e hinc := hinc.edge_mem
--   exists_vertex_inc e he := by

--     obtain ⟨v, hvinc⟩ := G.exists_vertex_inc he
--     use v
--   not_hypergraph x y z e hxinc hyinc hzinc := G.not_hypergraph hxinc hyinc hzinc
