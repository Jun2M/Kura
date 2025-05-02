import Kura.Subgraph
import Kura.Dep.Finset


open Set Function
variable {α α' β : Type*} {G H : Graph α β} {u v w : α} {e f g : β} {φ : α → α'} {x y z : α'}
namespace Graph


-- lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
--     (G.IncFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
--   classical
--   simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
--     Finsupp.single_apply, and_comm, ← incFun_ne_zero]

-- def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β :=
--   oftoMultiset (f '' G.V) (fun e ↦ (G.toMultiset e).map f) fun e v h ↦ (by
--     simp only [Multiset.mem_map, inc_iff_mem_toMultiset, mem_image] at h ⊢
--     obtain ⟨v, hv, rfl⟩ := h
--     use v, hv.vx_mem)

-- /-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
-- by applying a function `f : α → α'` to each vertex.
-- Edges between identified vertices become loops. -/
-- @[simps]
-- def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
--   V := f '' G.V
--   E := G.E
--   Inc₂ e x' y' := ∃ x y, G.Inc₂ e x y ∧ x' = f x ∧ y' = f y
--   inc₂_symm := by
--     rintro e - - ⟨x, y, h, rfl, rfl⟩
--     exact ⟨y, x, h.symm, rfl, rfl⟩
--   eq_or_eq_of_inc₂_of_inc₂ := by
--     rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
--     obtain rfl | rfl := hxy.left_eq_or_eq_of_inc₂ hzw <;> simp
--   edge_mem_iff_exists_inc₂ e := by
--     refine ⟨fun h ↦ ?_, ?_⟩
--     · obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet h
--       exact ⟨_, _, _, _, hxy, rfl, rfl⟩
--     rintro ⟨-, -, x, y, h, rfl, rfl⟩
--     exact h.edge_mem
--   vx_mem_left_of_inc₂ := by
--     rintro e - - ⟨x, y, h, rfl, rfl⟩
--     exact Set.mem_image_of_mem _ h.vx_mem_left

@[simps!]
def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β :=
  oftoMultiset (f '' G.V) (fun e ↦ (G.toMultiset e).map f) fun e v h ↦ (by
    simp only [Multiset.mem_map, inc_iff_mem_toMultiset, mem_image] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    use v, hv.vx_mem)

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc : (G.vxMap φ).Inc e x ↔ ∃ v, G.Inc e v ∧ φ v = x := by
  rw [← inc_iff_mem_toMultiset]
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]
  simp

@[simp]
lemma vxMap_toMultiset : (G.vxMap φ).toMultiset e = (G.toMultiset e).map φ := by
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]

@[simp]
lemma vxMap_inc₂' : (G.vxMap φ).Inc₂ e x y ↔ ∃ v w, G.Inc₂ e v w ∧ φ v = x ∧ φ w = y := by
  simp_rw [← toMultiset_eq_pair_iff, vxMap_toMultiset, Multiset.map_eq_pair_iff]

def edgePreimg {β' : Type*} (G : Graph α β) (σ : β' → β) : Graph α β' :=
  oftoMultiset G.V (G.toMultiset <| σ ·) (fun e v hv ↦ by
    simp only [inc_iff_mem_toMultiset] at hv
    exact hv.vx_mem)

variable {β' : Type*} {σ : β' → β}

@[simp] lemma edgePreimg.V : (G.edgePreimg σ).V = G.V := rfl

@[simp] lemma edgePreimg.E : (G.edgePreimg σ).E = σ ⁻¹' G.E := by
  ext e
  simp only [edgePreimg, oftoMultiset_edgeSet, toMultiset_card_eq_two_iff, mem_setOf_eq, mem_preimage]

@[simp]
lemma edgePreimg.Inc {e' : β'} : (G.edgePreimg σ).Inc e' u ↔ ∃ e, σ e' = e ∧ G.Inc e u := by
  simp only [edgePreimg, exists_eq_left']
  rw [← inc_iff_mem_toMultiset, oftoMultiset_toMultiset, inc_iff_mem_toMultiset]
  rintro e
  apply toMultiset_card_or

@[simp]
lemma edgePreimg.Inc₂ {e' : β'} : (G.edgePreimg σ).Inc₂ e' u v ↔ ∃ e, σ e' = e ∧ G.Inc₂ e u v := by
  simp only [edgePreimg, exists_eq_left']
  rw [← toMultiset_eq_pair_iff, oftoMultiset_toMultiset, toMultiset_eq_pair_iff]
  rintro e
  apply toMultiset_card_or
