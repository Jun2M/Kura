import Kura.Le


open Set Function
variable {α α' β : Type*} {G H : Graph α β} {u v w : α} {e f g : β} {φ : α → α'} {x y z : α'}
namespace Graph


lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
    (G.IncFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
  classical
  simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
    Finsupp.single_apply, and_comm, ← incFun_ne_zero]

def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β :=
  oftoMultiset (f '' G.V) (fun e ↦ (G.toMultiset e).map f) fun e v h ↦ (by
    simp only [Multiset.mem_map, inc_iff_mem_toMultiset, mem_image] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    use v, hv.vx_mem)

@[simp]
lemma vxMap.V : (G.vxMap φ).V = φ '' G.V := rfl

@[simp]
lemma vxMap.E : (G.vxMap φ).E = G.E := by simp [vxMap]

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc_iff : (G.vxMap φ).Inc e x ↔ ∃ v, G.Inc e v ∧ φ v = x := by
  rw [← inc_iff_mem_toMultiset]
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]
  simp

@[simp]
lemma vxMap_toMultiset_eq_map_toMultiset : (G.vxMap φ).toMultiset e = (G.toMultiset e).map φ := by
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]

lemma Inc₂.vxMap_of_inc₂ (hBtw : G.Inc₂ e u v) (φ : α → α') : (G.vxMap φ).Inc₂ e (φ u) (φ v) := by
  rw [inc₂_iff_toMultiset] at hBtw
  unfold vxMap
  rw [inc₂_iff_toMultiset, oftoMultiset_toMultiset (by simp [em]), hBtw]
  rfl

@[simp]
lemma vxMap_inc₂_iff : (G.vxMap φ).Inc₂ e x y ↔ ∃ x', φ x' = x ∧ ∃ y', φ y' = y ∧ G.Inc₂ e x' y' := by
  classical
  simp_rw [inc₂_iff_toMultiset]
  rw [vxMap, oftoMultiset_toMultiset (by simp [em])]
  constructor
  · rintro h
    simp only [Multiset.insert_eq_cons] at h
    simp_rw [← Multiset.map_eq_cons, Multiset.map_eq_singleton] at h
    obtain ⟨a, ha, rfl, b, hb, rfl⟩ := h
    use a, rfl, b, rfl
    obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem ha
    rw [hm, Multiset.erase_cons_head] at hb
    rwa [hb] at hm
  · rintro ⟨x', rfl, y', rfl, hBtw⟩
    rw [hBtw]
    rfl



def edgePreimg {β' : Type*} (G : Graph α β) (σ : β' → β) : Graph α β' :=
  oftoMultiset G.V (G.toMultiset <| σ ·) (fun e v hv ↦ by
    simp only [inc_iff_mem_toMultiset] at hv
    exact hv.vx_mem)

variable {β' : Type*} {σ : β' → β}

@[simp] lemma edgePreimg.V : (G.edgePreimg σ).V = G.V := rfl

@[simp] lemma edgePreimg.E : (G.edgePreimg σ).E = σ ⁻¹' G.E := by
  ext e
  simp only [edgePreimg, oftoMultiset_E, toMultiset_card_eq_two_iff, mem_setOf_eq, mem_preimage]

@[simp]
lemma edgePreimg.Inc {e' : β'} : (G.edgePreimg σ).Inc e' u ↔ ∃ e, σ e' = e ∧ G.Inc e u := by
  simp only [edgePreimg, exists_eq_left']
  rw [← inc_iff_mem_toMultiset, oftoMultiset_toMultiset, inc_iff_mem_toMultiset]
  rintro e
  apply toMultiset_card_or

@[simp]
lemma edgePreimg.Inc₂ {e' : β'} : (G.edgePreimg σ).Inc₂ e' u v ↔ ∃ e, σ e' = e ∧ G.Inc₂ e u v := by
  simp only [edgePreimg, exists_eq_left']
  rw [inc₂_iff_toMultiset, oftoMultiset_toMultiset, inc₂_iff_toMultiset]
  rintro e
  apply toMultiset_card_or
