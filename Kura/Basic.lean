import Mathlib.Algebra.BigOperators.Sym
import Kura.Dep.Rel

variable {α β : Type*}

open Set Function

structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  Inc : α → β → Prop
  vx_mem_of_inc : ∀ ⦃v e⦄, Inc v e → v ∈ V
  edge_mem_of_inc : ∀ ⦃v e⦄, Inc v e → e ∈ E
  exists_vertex_inc : ∀ ⦃e⦄, e ∈ E → ∃ v, Inc v e
  not_hypergraph : ∀ ⦃x y z e⦄, Inc x e → Inc y e → Inc z e → x = y ∨ y = z ∨ x = z

-- @[repr]
-- instance : Repr (Graph α β) where
--   reprPrec G n := s!"Graph.mk {G.V} {G.E}"

variable {G : Graph α β} {u v w x y : α} {e f g : β}

namespace Graph

lemma Inc.vx_mem (h : G.Inc x e) : x ∈ G.V := G.vx_mem_of_inc h

lemma Inc.edge_mem (h : G.Inc x e) : e ∈ G.E := G.edge_mem_of_inc h

@[ext]
lemma ext {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (hInc : ∀ x e, G₁.Inc x e ↔ G₂.Inc x e) : G₁ = G₂ := by
  obtain ⟨hV, hE, hInc, hvx, hex, hex, hnh⟩ := G₁
  obtain ⟨hV', hE', hInc', hvx', hex', hex', hnh'⟩ := G₂
  simp only at hV hE hInc
  simp only [hV, hE, mk.injEq, true_and]
  ext x e
  exact hInc x e

abbrev IsLoop (G : Graph α β) (e : β) := ∃! x, G.Inc x e

lemma IsLoop.mem {G : Graph α β} {e : β} (h : G.IsLoop e) : e ∈ G.E := by
  obtain ⟨v, hv, h⟩ := h
  exact G.edge_mem_of_inc hv

lemma exist_two_of_not_loop {G : Graph α β} {e : β} (he : e ∈ G.E) (h : ¬G.IsLoop e) :
    ∃ x y, x ≠ y ∧ G.Inc x e ∧ G.Inc y e := by
  simp only [IsLoop, ExistsUnique, not_exists, not_and, not_forall, Classical.not_imp] at h
  choose v hv using G.exists_vertex_inc he
  choose w hw h using h v hv
  use v, w, ((ne_eq _ _).mpr h).symm

@[mk_iff]
structure IsBetween (G : Graph α β) (e : β) (x y : α) : Prop where
  inc_left : G.Inc x e
  inc_right : G.Inc y e
  isLoop_of_eq : x = y → G.IsLoop e

lemma IsBetween.symm (h : G.IsBetween e x y) : G.IsBetween e y x where
  inc_left := h.inc_right
  inc_right := h.inc_left
  isLoop_of_eq h' := h.isLoop_of_eq h'.symm

lemma IsBetween.comm : G.IsBetween e x y ↔ G.IsBetween e y x := by
  refine ⟨IsBetween.symm, IsBetween.symm⟩

lemma IsBetween.vx_mem_left (h : G.IsBetween e x y) : x ∈ G.V :=
  h.inc_left.vx_mem

lemma IsBetween.vx_mem_right (h : G.IsBetween e x y) : y ∈ G.V :=
  h.inc_right.vx_mem

lemma IsBetween.edge_mem (h : G.IsBetween e x y) : e ∈ G.E :=
  h.inc_left.edge_mem

def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, G.IsBetween e x y

lemma Adj.comm : G.Adj x y ↔ G.Adj y x := by
  unfold Adj
  constructor <;>
  · rintro ⟨e, h⟩
    exact ⟨e, h.symm⟩

lemma Adj.mem {G : Graph α β} {x y : α} (h : G.Adj x y) : x ∈ G.V := by
  obtain ⟨e, hinc, hif⟩ := h
  exact G.vx_mem_of_inc hinc

lemma Adj.mem' {G : Graph α β} {x y : α} (h : G.Adj x y) : y ∈ G.V := by
  rw [Adj.comm] at h
  exact Adj.mem h

lemma not_adj_of_not_mem {G : Graph α β} {x y : α} (h : x ∉ G.V) : ¬G.Adj x y := by
  rintro ⟨e, hinc, hif⟩
  have hx' := G.vx_mem_of_inc hinc
  exact h hx'

lemma not_adj_of_not_mem' {G : Graph α β} {x y : α} (h : y ∉ G.V) : ¬G.Adj x y := by
  rw [Adj.comm]
  exact not_adj_of_not_mem h

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc v e}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}




@[simp]
def reflAdj (G : Graph α β) :=
  fun x y ↦ ite (x = y) (h := Classical.dec _) (x ∈ G.V) (∃ e, G.Inc x e ∧ G.Inc y e)

lemma reflAdj_of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
  simpa only [reflAdj, ↓reduceIte]

lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj_of_vxMem h

lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
  unfold reflAdj at h ⊢
  split_ifs with hxy
  · subst y
    simpa only [↓reduceIte] using h
  · simp only [((ne_eq _ _).mpr hxy).symm, ↓reduceIte] at h
    simpa only [and_comm]

lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
  refine ⟨reflAdj.symm, reflAdj.symm⟩

lemma Inc.reflAdj_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.reflAdj x y := by
  unfold reflAdj
  split_ifs with hxy
  · subst y
    exact hx.vx_mem
  · use e

lemma reflAdj.mem (h : G.reflAdj x y) : x ∈ G.V := by
  unfold reflAdj at h
  split_ifs at h with hxy
  · exact h
  · rcases h with ⟨e, hincx, hincy⟩
    exact G.vx_mem_of_inc hincx

lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
  obtain ⟨e, hincx, hincy⟩ := h
  sorry
  -- split_ifs at hincy with hxy
  -- · subst y
  --   exact Inc.reflAdj_of_inc hincx hincx
  -- · simp only [Graph.reflAdj, hxy, ↓reduceIte]
  --   use e

lemma reflAdj.Adj_or_eq (h : reflAdj G x y) : G.Adj x y ∨ x = y ∧ x ∈ G.V := by
  unfold reflAdj at h
  split_ifs at h with hxy
  · subst y
    exact Or.inr ⟨rfl, h⟩
  sorry
  -- · left
  --   obtain ⟨e, hincx, hincy⟩ := h
  --   use e, hincx
  --   simp only [hxy, ↓reduceIte, hincy]

lemma reflAdj_iff_adj_or_eq : G.reflAdj x y ↔ G.Adj x y ∨ x = y ∧ x ∈ G.V := by
  refine ⟨reflAdj.Adj_or_eq, ?_⟩
  by_cases h : x = y
  · subst y
    simp only [true_and, reflAdj, ↓reduceIte, or_imp, imp_self, and_true]
    exact fun a ↦ Adj.mem a
  · rintro (h | ⟨rfl, h⟩)
    · exact h.reflAdj
    · simp only [not_true_eq_false] at h




def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| reflAdj_of_vxMem hx

lemma Inc.connected_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.Connected x y :=
  reflAdj.connected (hx.reflAdj_of_inc hy)

lemma connected_comm {G : Graph α β} {x y : α} : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  have := Relation.TransGen.symmetric (r := G.reflAdj) ?_
  constructor <;> exact fun h ↦ this h
  rintro x y hradj
  exact hradj.symm

lemma Connected.refl {G : Graph α β} {x : α} (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

lemma Connected.symm {G : Graph α β} {x y : α} (h : G.Connected x y) : G.Connected y x := by
  rwa [connected_comm]

lemma Connected.trans {G : Graph α β} {x y z : α} (hxy : G.Connected x y) (hyz : G.Connected y z) :
    G.Connected x z := Relation.TransGen.trans hxy hyz

@[simp]
def ConnSetoid (G : Graph α β) : Setoid G.V where
  r x y := G.Connected x y
  iseqv := by
    constructor
    · rintro ⟨x, hx⟩
      exact Connected.refl hx
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hconn
      exact hconn.symm
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hxy hyz
      exact hxy.trans hyz

lemma Connected.mem {G : Graph α β} {x y : α} (hconn : G.Connected x y) : x ∈ G.V := by
  simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
  obtain ⟨a, hradj, hTG⟩ := hconn
  exact hradj.mem

lemma Connected.mem' {G : Graph α β} {x y : α} (hconn : G.Connected x y) : y ∈ G.V := by
  rw [connected_comm] at hconn
  exact hconn.mem

lemma not_connected_of_not_mem {G : Graph α β} {x y : α} (h : x ∉ G.V) : ¬G.Connected x y := by
  contrapose! h
  exact h.mem

lemma not_connected_of_not_mem' {G : Graph α β} {x y : α} (h : y ∉ G.V) : ¬G.Connected x y := by
  rw [connected_comm]
  exact not_connected_of_not_mem h


lemma not_inc_of_E_empty (hE : G.E = ∅) : ¬ G.Inc v e := by
  intro hinc
  exact (hE ▸ hinc.edge_mem : e ∈ ∅)

lemma not_adj_of_no_inc_edge (hnoinc : ∀ e, ¬ G.Inc u e) : ¬ G.Adj u v := by
  rintro ⟨e, hinc, hif⟩
  exact hnoinc e hinc

lemma reflAdj_iff_eq_and_mem_of_no_inc_edge (hnoinc : ∀ e, ¬ G.Inc u e) : G.reflAdj u v ↔ u = v ∧ u ∈ G.V := by
  rw [reflAdj_iff_adj_or_eq]
  simp only [not_adj_of_no_inc_edge hnoinc, false_or]

lemma eq_no_inc_edge_of_reflAdj_of (hnoinc : ∀ e, ¬ G.Inc u e) (h : G.reflAdj u v) : u = v := by
  rw [reflAdj_iff_eq_and_mem_of_no_inc_edge hnoinc] at h
  exact h.1

lemma eq_of_no_inc_edge_of_connected (hnoinc : ∀ e, ¬ G.Inc u e) (h : G.Connected u v) : u = v := by
  induction h with
  | single hradj => exact eq_no_inc_edge_of_reflAdj_of hnoinc hradj
  | tail w hconn ih =>
    subst ih
    exact eq_no_inc_edge_of_reflAdj_of hnoinc hconn

lemma connected_iff_eq_and_mem_no_inc_edge (hnoinc : ∀ e, ¬ G.Inc u e) :
    G.Connected u v ↔ u = v ∧ u ∈ G.V := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨eq_of_no_inc_edge_of_connected hnoinc h, h.mem⟩
  · rintro ⟨rfl, h⟩
    exact connected_self h


noncomputable def toSym2 (G : Graph α β) {e : β} (he : e ∈ G.E) : Sym2 α := by
  by_cases h : G.IsLoop e
  · choose v hv using h
    exact s(v, v)
  · choose x y h using (exist_two_of_not_loop he h)
    exact s(x, y)

lemma exists_mem_toSym2_iff_inc {G : Graph α β} {e : β} {y : α} :
    (∃ (he : e ∈ G.E), y ∈ G.toSym2 he) ↔ G.Inc y e := by
  by_cases h : G.IsLoop e
  · simp only [toSym2, h, ↓reduceDIte, Sym2.mem_iff, or_self, exists_prop]
    obtain ⟨hinc, heq⟩ := h.choose_spec
    constructor
    · rintro ⟨he, rfl⟩
      exact hinc
    · rintro h
      exact ⟨G.edge_mem_of_inc h, heq _ h⟩
  · simp only [toSym2, h, ↓reduceDIte, ne_eq, Sym2.mem_iff]
    constructor
    · rintro ⟨he, hor⟩
      obtain ⟨H1, H2, H3⟩ := (G.exist_two_of_not_loop he h).choose_spec.choose_spec
      cases hor <;> subst y <;> assumption
    · rintro hinc
      have he := G.edge_mem_of_inc hinc
      use he
      obtain ⟨H1, H2, H3⟩ := (G.exist_two_of_not_loop he h).choose_spec.choose_spec
      have heqor := G.not_hypergraph hinc H2 H3
      simpa only [ne_eq, H1, false_or] using heqor

@[simp]
lemma mem_toSym2_iff_inc {G : Graph α β} {e : β} {y : α} (he : e ∈ G.E):
    y ∈ G.toSym2 he ↔ G.Inc y e := by
  rw [← exists_mem_toSym2_iff_inc]
  simp only [he, exists_true_left]

@[simp]
lemma mem_toSym2_of_inc {G : Graph α β} {e : β} {y : α} (h : G.Inc y e) :
    y ∈ G.toSym2 (G.edge_mem_of_inc h) := by
  rw [← exists_mem_toSym2_iff_inc] at h
  obtain ⟨he, h⟩ := h
  exact h

@[simp]
lemma mem_of_mem_toSym2 {G : Graph α β} {e : β} {y : α} (he : e ∈ G.E) (h : y ∈ G.toSym2 he) :
    y ∈ G.V := by
  apply G.vx_mem_of_inc
  rw [← exists_mem_toSym2_iff_inc]
  use he
