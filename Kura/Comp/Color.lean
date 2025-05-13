import Kura.Connected
import Kura.Walk.Path
import Mathlib.Order.SymmDiff


open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph

structure IsColoring (G : Graph α β) (f : α → ℕ) (n : ℕ) : Prop where
  proper ⦃u v : _⦄ : G.Adj u v → f u ≠ f v
  uptoN ⦃u : _⦄ : u ∈ V(G) → f u < n

def Colorable (G : Graph α β) (n : ℕ) : Prop := ∃ f : α → ℕ, IsColoring G f n

lemma zero_colorable_iff : G.Colorable 0 ↔ G = ⊥ := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, ?_⟩
  · rw [← vertexSet_empty_iff_eq_bot]
    by_contra! hV
    simpa using hf.uptoN hV.some_mem
  · rintro rfl
    use fun _ ↦ 0, by simp, by simp

lemma one_colorable_iff : G.Colorable 1 ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, ?_⟩
  · rw [← edgeSet_empty_iff_eq_noEdge]
    by_contra! hE
    obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet hE.some_mem
    have hu := hf.uptoN huv.vx_mem_left
    have hv := hf.uptoN huv.vx_mem_right
    simp at hu hv
    simpa [hu, hv] using hf.proper ⟨hE.some, huv⟩
  · rintro h
    rw [h]
    use fun _ ↦ 0, by simp, by simp
 

class Bipartite (G : Graph α β) where
  color : α → ℕ
  proper ⦃u v : _⦄ : G.Adj u v → color u ≠ color v
  two : ∀ u, color u < 2

def color (G : Graph α β) [G.Bipartite] : α → ℕ := Bipartite.color G
def proper (G : Graph α β) [hBip : G.Bipartite] {u v} : G.Adj u v → color G u ≠ color G v :=
  (hBip.proper ·)
def twoColor (G : Graph α β) [hBip : G.Bipartite] : ∀ u, color G u < 2 := hBip.two

lemma color_zero_or_one (G : Graph α β) [G.Bipartite] (u : α) :
    G.color u = 0 ∨ G.color u = 1 := by
  have := G.twoColor u
  interval_cases (G.color u) <;> simp

@[simp]
lemma color_ne_zero (G : Graph α β) [G.Bipartite] : G.color u ≠ 0 ↔ G.color u = 1 :=
  ⟨fun h ↦ by simpa [h] using color_zero_or_one G u, fun h ↦ by simp [h]⟩

@[simp]
lemma color_ne_one (G : Graph α β) [G.Bipartite] : G.color u ≠ 1 ↔ G.color u = 0 :=
  G.color_ne_zero.not_right.symm

@[simp]
lemma Inc₂.ne (G : Graph α β) [G.Bipartite] {u v : α} (huv : G.Inc₂ e u v) : u ≠ v := by
  rintro rfl
  simpa using G.proper ⟨e, huv.symm⟩

lemma Inc₂.color_eq_zero (G : Graph α β) [G.Bipartite] {u v : α} (huv : G.Inc₂ e u v) :
    G.color u = 0 ↔ G.color v = 1 := by
  constructor <;> rintro h
  · have := h ▸ G.proper ⟨e, huv.symm⟩
    simpa using this
  · have := h ▸ G.proper ⟨e, huv⟩
    simpa using this

lemma Inc₂.color_eq_one (G : Graph α β) [G.Bipartite] {u v : α} (huv : G.Inc₂ e u v) :
    G.color u = 1 ↔ G.color v = 0 := (color_eq_zero G huv.symm).symm

lemma Inc₂.color_ne_zero (G : Graph α β) [G.Bipartite] {u v : α} (huv : G.Inc₂ e u v) :
    G.color u ≠ 0 ↔ G.color v = 0 := by
  simp only [ne_eq, Graph.color_ne_zero]
  exact color_eq_one G huv

lemma Inc₂.color_ne_one (G : Graph α β) [G.Bipartite] {u v : α} (huv : G.Inc₂ e u v) :
    G.color u ≠ 1 ↔ G.color v = 1 := by
  simp only [ne_eq, Graph.color_ne_one]
  exact color_eq_zero G huv

lemma exists_ends (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) :
    ∃ u v, u ≠ v ∧ G.Inc₂ e u v ∧ G.color u = 0 ∧ G.color v = 1 := by
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet he
  wlog hu0 : G.color u = 0 generalizing u v
  · apply this v u huv.symm
    rwa [← ne_eq, huv.color_ne_zero] at hu0
  exact ⟨u, v, huv.ne, huv, hu0, (huv.color_eq_zero).mp hu0⟩

noncomputable def zeroVx (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) : α :=
  (G.exists_ends he).choose

noncomputable def oneVx (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) : α :=
  (G.exists_ends he).choose_spec.choose

lemma zeroVx_ne_oneVx (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) :
    G.zeroVx he ≠ G.oneVx he := (G.exists_ends he).choose_spec.choose_spec.left

lemma inc₂_zeroVx_oncVx (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) :
    G.Inc₂ e (G.zeroVx he) (G.oneVx he) := (G.exists_ends he).choose_spec.choose_spec.right.left

lemma zeroVx_color_zero (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) :
    G.color (G.zeroVx he) = 0 := (G.exists_ends he).choose_spec.choose_spec.right.right.left

lemma oneVx_color_one (G : Graph α β) [G.Bipartite] (he : e ∈ E(G)) :
    G.color (G.oneVx he) = 1 := (G.exists_ends he).choose_spec.choose_spec.right.right.right
