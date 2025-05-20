import Kura.Subgraph
import Kura.Dep.Finset


open Set Function
variable {α α' β : Type*} {G H : Graph α β} {u v w : α} {e f g : β} {φ φ': α → α'} {x y z : α'}
namespace Graph


-- lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
--     (G.IncFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
--   classical
--   simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
--     Finsupp.single_apply, and_comm, ← incFun_ne_zero]

-- def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β :=
--   oftoMultiset (f '' V(G)) (fun e ↦ (G.toMultiset e).map f) fun e v h ↦ (by
--     simp only [Multiset.mem_map, inc_iff_mem_toMultiset, mem_image] at h ⊢
--     obtain ⟨v, hv, rfl⟩ := h
--     use v, hv.vx_mem)

-- /-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
-- by applying a function `f : α → α'` to each vertex.
-- Edges between identified vertices become loops. -/
-- @[simps]
-- def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
--   V := f '' V(G)
--   E := E(G)
--   IsLink e x' y' := ∃ x y, G.IsLink e x y ∧ x' = f x ∧ y' = f y
--   isLink_symm := by
--     rintro e - - ⟨x, y, h, rfl, rfl⟩
--     exact ⟨y, x, h.symm, rfl, rfl⟩
--   eq_or_eq_of_isLink_of_isLink := by
--     rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
--     obtain rfl | rfl := hxy.left_eq_or_eq_of_isLink hzw <;> simp
--   edge_mem_iff_exists_isLink e := by
--     refine ⟨fun h ↦ ?_, ?_⟩
--     · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
--       exact ⟨_, _, _, _, hxy, rfl, rfl⟩
--     rintro ⟨-, -, x, y, h, rfl, rfl⟩
--     exact h.edge_mem
--   vx_mem_left_of_isLink := by
--     rintro e - - ⟨x, y, h, rfl, rfl⟩
--     exact Set.mem_image_of_mem _ h.vx_mem_left

@[simps! vertexSet edgeSet]
noncomputable def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β :=
  oftoMultiset (f '' V(G)) (fun e ↦ (G.toMultiset e).map f) fun e v h ↦ (by
    simp only [Multiset.mem_map, inc_iff_mem_toMultiset, mem_image] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    use v, hv.vx_mem)

scoped infix:50 " '' " => fun f G ↦ vxMap G f

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc : (φ '' G).Inc e x ↔ ∃ v, G.Inc e v ∧ φ v = x := by
  rw [← inc_iff_mem_toMultiset]
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]
  simp

@[simp]
lemma vxMap_toMultiset : (φ '' G).toMultiset e = (G.toMultiset e).map φ := by
  unfold vxMap
  rw [oftoMultiset_toMultiset (by simp [em])]

@[simp]
lemma vxMap_isLink : (φ '' G).IsLink e x y ↔ ∃ v, φ v = x ∧ ∃ w, φ w = y ∧ G.IsLink e v w := by
  simp_rw [← toMultiset_eq_pair_iff, vxMap_toMultiset, Multiset.map_eq_pair_iff]

lemma vxMap_isLink_toMultiset : (φ '' G).IsLink e x y ↔ (G.toMultiset e).map φ = {x, y} := Iff.rfl

lemma vxMap_eq_vxMap_of_eqOn (h : EqOn φ φ' V(G)) : (φ '' G) = (φ' '' G) := by
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [vxMap_vertexSet, vxMap_vertexSet]
    exact image_congr h
  · simp_rw [vxMap_isLink]
    refine ⟨fun ⟨v, hv, w, hw, hvw⟩ ↦ ?_, fun ⟨v, hv, w, hw, hvw⟩ ↦ ?_⟩
    · use v, (h hvw.vx_mem_left).symm.trans hv, w, (h hvw.vx_mem_right).symm.trans hw, hvw
    · use v, (h hvw.vx_mem_left).trans hv, w, (h hvw.vx_mem_right).trans hw, hvw


@[simps! vertexSet edgeSet]
noncomputable def edgePreimg {β' : Type*} (G : Graph α β) (σ : β' → β) : Graph α β' :=
  oftoMultiset V(G) (G.toMultiset <| σ ·) (fun e v hv ↦ by
    simp only [inc_iff_mem_toMultiset] at hv
    exact hv.vx_mem)

variable {β' : Type*} {σ : β' → β}

@[simp]
lemma edgePreimg.Inc {e' : β'} : (G.edgePreimg σ).Inc e' u ↔ ∃ e, σ e' = e ∧ G.Inc e u := by
  simp only [edgePreimg, exists_eq_left']
  rw [← inc_iff_mem_toMultiset, oftoMultiset_toMultiset, inc_iff_mem_toMultiset]
  rintro e
  apply toMultiset_card_or

@[simp]
lemma edgePreimg.IsLink {e' : β'} : (G.edgePreimg σ).IsLink e' u v ↔ ∃ e, σ e' = e ∧ G.IsLink e u v := by
  simp only [edgePreimg, exists_eq_left']
  rw [← toMultiset_eq_pair_iff, oftoMultiset_toMultiset, toMultiset_eq_pair_iff]
  rintro e
  apply toMultiset_card_or


variable {β' : Type*} {σ : β → β'} {e' : β'}

@[simps! vertexSet]
def edgeMap (G : Graph α β) (σ : β → β') (hσ : InjOn σ E(G)) : Graph α β' :=
  Graph.ofInc V(G) (fun e' x ↦ ∃ e, σ e = e' ∧ G.Inc e x) (fun e' x ⟨e, heq, hinc⟩ ↦ hinc.vx_mem)
  (fun x y z e' ⟨e₁, heq₁, hinc₁⟩ ⟨e₂, heq₂, hisLink⟩ ⟨e₃, heq₃, hinc₃⟩ ↦ by
    obtain rfl := hσ hinc₁.edge_mem hisLink.edge_mem <| heq₁.trans heq₂.symm
    obtain rfl := hσ hisLink.edge_mem hinc₃.edge_mem <| heq₂.trans heq₃.symm
    exact hinc₁.eq_or_eq_or_eq_of_inc_of_inc hisLink hinc₃)

@[simp]
lemma edgeMap_edgeSet (hσ : InjOn σ E(G)) : (G.edgeMap σ hσ).edgeSet = σ '' E(G) := by
  ext e'
  simp only [edgeMap, ofInc_E, mem_setOf_eq, mem_image]
  refine ⟨fun ⟨x, e, heq, hinc⟩ ↦ ⟨e, hinc.edge_mem, heq⟩, fun ⟨e, he, heq⟩ ↦ ?_⟩
  obtain ⟨x, hinc⟩ := exists_inc_of_mem_edgeSet he
  use x, e

@[simp]
lemma edgeMap_inc (hσ : InjOn σ E(G)) : (G.edgeMap σ hσ).Inc e' u ↔ ∃ e, σ e = e' ∧ G.Inc e u := by
  simp only [edgeMap, ofInc_inc]

@[simp]
lemma edgeMap_isLink (hσ : InjOn σ E(G)) : (G.edgeMap σ hσ).IsLink e' u v ↔ ∃ e, σ e = e' ∧ G.IsLink e u v := by
  simp only [edgeMap, ofInc, forall_exists_index, and_imp, mk'_isLink]
  simp_rw [isLink_iff_inc]
  refine ⟨fun ⟨⟨e, heq1, hinc1⟩, ⟨f, heq2, hinc2⟩, h⟩ ↦ ?_, fun ⟨e, heq, hincu, hincv, h⟩ ↦ ?_⟩
  · obtain rfl := hσ hinc1.edge_mem hinc2.edge_mem <| heq1.trans heq2.symm
    use e, heq1, hinc1, hinc2, (h · e heq1)
  · use ⟨e, heq, hincu⟩, ⟨e, heq, hincv⟩, fun x f hfeq hfinc ↦ ?_
    obtain rfl := hσ hfinc.edge_mem hincv.edge_mem <| hfeq.trans heq.symm
    exact h x hfinc


@[simps! vertexSet isLink]
def map (G : Graph α β) (f : α → α') (g : β → β') (h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂)
    (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ → (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f) : Graph α' β' :=
  Graph.mk' (f '' V(G)) (fun e x y ↦ ∃ e', g e' = e ∧ ∃ x', f x' = x ∧ ∃ y', f y' = y ∧ G.IsLink e' x' y')
  (fun e x y ⟨e', he', x', hx', y', hy', hbtw⟩ ↦ ⟨e', he', y', hy', x', hx', hbtw.symm⟩)
  (fun e x y a b hxy hab ↦ by
    obtain ⟨e', he', x', rfl, y', rfl, hbtw⟩ := hxy
    obtain ⟨e'', rfl, a', rfl, b', rfl, hbtw'⟩ := hab
    have := h e' hbtw.edge_mem e'' hbtw'.edge_mem he'
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := by simpa [hbtw.toSym2, hbtw'.toSym2] using this
    tauto
    tauto)
  (fun e x y ⟨e', he', x', hx', y', hy', hbtw⟩ ↦ ⟨x', hbtw.vx_mem_left, hx'⟩)

variable {G : Graph α β} {f : α → α'} {g : β → β'} {h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂)
    (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ → (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f}

@[simp]
lemma map_edgeSet : E(G.map f g h) = g '' E(G) := by
  ext e'
  simp only [map, mk'_edgeSet, mem_setOf_eq, mem_image]
  refine ⟨fun ⟨a', b', e, heq', a, heqa, b, heqb, hbtw⟩ ↦ ?_, fun ⟨e, he, heq⟩ ↦ ?_⟩
  · subst heq' heqa heqb
    use e, hbtw.edge_mem
  · subst heq
    obtain ⟨a, b, hbtw⟩ := exists_inc_of_mem_edgeSet he
    use f a, f b, e, rfl, a, rfl, b, rfl, hbtw

lemma IsLink.map (hbtw : G.IsLink e u v) : (G.map f g h).IsLink (g e) (f u) (f v) := by
  rw [map_isLink]
  use e, rfl, u, rfl, v, rfl, hbtw

lemma mem_vertexSet_map (hin : u ∈ V(G)) : f u ∈ V(G.map f g h) := by
  rw [map_vertexSet]
  exact ⟨u, hin, rfl⟩

lemma mem_edgeSet_map (hin : e ∈ E(G)) : g e ∈ E(G.map f g h) := by
  rw [map_edgeSet]
  use e

lemma map_eq_vxMap (f : α → α') : G.map f id (fun e₁ he₁ e₂ he₂ heq ↦ by simp_all) = (f '' G) := by
  ext a b c
  · simp
  · simp only [map_isLink, id_eq, exists_eq_left, vxMap_isLink]
