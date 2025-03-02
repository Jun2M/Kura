import Mathlib
import Kura.Dep.Quot
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

def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, G.Inc x e ∧ ite (x = y) (h := Classical.dec _) (G.IsLoop e) (G.Inc y e)

lemma adj_comm : G.Adj x y ↔ G.Adj y x := by
  unfold Adj
  by_cases h : x = y
  · simp only [h, ↓reduceIte]
  · simp only [h, ((ne_eq _ _).mpr h).symm, ↓reduceIte, and_comm]

lemma mem_of_adj {G : Graph α β} {x y : α} (h : G.Adj x y) : x ∈ G.V := by
  obtain ⟨e, hinc, hif⟩ := h
  exact G.vx_mem_of_inc hinc

lemma mem_of_adj' {G : Graph α β} {x y : α} (h : G.Adj x y) : y ∈ G.V := by
  rw [adj_comm] at h
  exact mem_of_adj h

lemma not_adj_of_not_mem {G : Graph α β} {x y : α} (h : x ∉ G.V) : ¬G.Adj x y := by
  rintro ⟨e, hinc, hif⟩
  have hx' := G.vx_mem_of_inc hinc
  exact h hx'

lemma not_adj_of_not_mem' {G : Graph α β} {x y : α} (h : y ∉ G.V) : ¬G.Adj x y := by
  rw [adj_comm]
  exact not_adj_of_not_mem h

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc v e}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}



def Connected (G : Graph α β) := Relation.TransGen (fun x y ↦ G.Adj x y ∨ x = y ∧ x ∈ G.V)

lemma Adj.connected (h : G.Adj x y) : G.Connected x y :=
  Relation.TransGen.single <| .inl h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| .inr ⟨rfl, hx⟩

lemma Inc.connected_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.Connected x y := by
  by_cases h : x = y
  · subst y
    exact connected_self (G.vx_mem_of_inc hx)
  · apply Adj.connected
    simp only [Adj, h, ↓reduceIte]
    use e

lemma connected_comm {G : Graph α β} {x y : α} : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  have := Relation.TransGen.symmetric (r := (fun x y ↦ G.Adj x y ∨ x = y ∧ x ∈ G.V)) ?_
  constructor <;> exact fun h ↦ this h
  rintro x y (hadj | ⟨rfl, hxin⟩)
  · rw [adj_comm] at hadj
    exact Or.inl hadj
  · right
    simp only [hxin, and_self]

lemma Connected.refl {G : Graph α β} {x : α} (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

lemma Connected.symm {G : Graph α β} {x y : α} (h : G.Connected x y) : G.Connected y x := by
  rwa [connected_comm]

lemma Connected.trans {G : Graph α β} {x y z : α} (hxy : G.Connected x y) (hyz : G.Connected y z) :
    G.Connected x z := Relation.TransGen.trans hxy hyz

lemma Connected.mem {G : Graph α β} {x y : α} (hconn : G.Connected x y) : x ∈ G.V := by
  simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
  obtain ⟨a, (hadj | ⟨rfl, hxin⟩), hTG⟩ := hconn
  · exact mem_of_adj hadj
  · exact hxin

lemma Connected.mem' {G : Graph α β} {x y : α} (hconn : G.Connected x y) : y ∈ G.V := by
  rw [connected_comm] at hconn
  exact hconn.mem

lemma not_connected_of_not_mem {G : Graph α β} {x y : α} (h : x ∉ G.V) : ¬G.Connected x y := by
  contrapose! h
  exact h.mem

lemma not_connected_of_not_mem' {G : Graph α β} {x y : α} (h : y ∉ G.V) : ¬G.Connected x y := by
  rw [connected_comm]
  exact not_connected_of_not_mem h


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
