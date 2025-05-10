import Kura.Connected
import Kura.Walk.Path
import Mathlib.Order.SymmDiff


open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph

structure IsColoring (G : Graph α β) (f : α → ℕ) (n : ℕ) : Prop where
  proper ⦃u v⦄ : G.Adj u v → f u ≠ f v
  uptoN ⦃u⦄ : f u < n

def Colorable (G : Graph α β) (n : ℕ) : Prop := ∃ f : α → ℕ, IsColoring G f n

class Bipartite (G : Graph α β) where
  color : α → ℕ
  proper ⦃u v⦄ : G.Adj u v → color u ≠ color v
  two : ∀ u, color u < 2

def color (G : Graph α β) [G.Bipartite] : α → ℕ := Bipartite.color G
def proper (G : Graph α β) [hBip : G.Bipartite] {u v} : G.Adj u v → color G u ≠ color G v :=
  (hBip.proper ·)
def two (G : Graph α β) [hBip : G.Bipartite] : ∀ u, color G u < 2 := hBip.two

lemma color_zero_or_one (G : Graph α β) [G.Bipartite] (u : α) :
    G.color u = 0 ∨ G.color u = 1 := by
  have := G.two u
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

lemma exists_ends (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) :
    ∃ u v, u ≠ v ∧ G.Inc₂ e u v ∧ G.color u = 0 ∧ G.color v = 1 := by
  obtain ⟨u, v, huv⟩ := Inc₂.exists_vx_inc₂ he
  wlog hu0 : G.color u = 0 generalizing u v
  · apply this v u huv.symm
    rwa [← ne_eq, huv.color_ne_zero] at hu0
  exact ⟨u, v, huv.ne, huv, hu0, (huv.color_eq_zero).mp hu0⟩

noncomputable def zeroVx (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) : α :=
  (G.exists_ends he).choose

noncomputable def oneVx (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) : α :=
  (G.exists_ends he).choose_spec.choose

lemma zeroVx_ne_oneVx (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) :
    G.zeroVx he ≠ G.oneVx he := (G.exists_ends he).choose_spec.choose_spec.left

lemma inc₂_zeroVx_oncVx (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) :
    G.Inc₂ e (G.zeroVx he) (G.oneVx he) := (G.exists_ends he).choose_spec.choose_spec.right.left

lemma zeroVx_color_zero (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) :
    G.color (G.zeroVx he) = 0 := (G.exists_ends he).choose_spec.choose_spec.right.right.left

lemma oneVx_color_one (G : Graph α β) [G.Bipartite] (he : e ∈ G.E) :
    G.color (G.oneVx he) = 1 := (G.exists_ends he).choose_spec.choose_spec.right.right.right

structure IsMatching (G : Graph α β) (F : Set β) : Prop where
  supp : F ⊆ G.E
  disj : ∀ e ∈ F, ∀ f ∈ F, e ≠ f → Disjoint (G.toMultiset e) (G.toMultiset f)

structure IsPerfectMatching (G : Graph α β) (F : Set β) : Prop where
  supp : F ⊆ G.E
  all_matched : ∀ v ∈ G.V, ∃! e ∈ F, G.Inc e v

lemma exists_isMatching (G : Graph α β) : ∃ M : Set β, G.IsMatching M :=
  ⟨∅, by constructor <;> simp [IsMatching]⟩

lemma exists_maximal_isMatching (G : Graph α β) [G.Finite] :
    ∃ M : Set β, Maximal G.IsMatching M := by
  obtain ⟨M, hM⟩ := exists_isMatching G
  obtain ⟨M, _hM, hMax⟩ := Set.Finite.exists_le_maximal (s := {s : Set β | s ⊆ G.E ∧ G.IsMatching s})
    (Finite.sep Graph.Finite.edge_fin.powerset G.IsMatching) ⟨hM.supp, hM⟩
  simp only [mem_setOf_eq] at hMax
  rw [maximal_and_iff_left_of_imp (fun M hM ↦ hM.supp)] at hMax
  exact ⟨M, hMax.right⟩

lemma IsPerfectMatching_supported (G : Graph α β) (F : Set β) :
    G.IsPerfectMatching (G.E ∩ F) ↔ G.IsPerfectMatching F := by
  sorry

def IsMatching.VxMatched (G : Graph α β) (M : Set β) (v : α) : Prop :=
  ∃ e ∈ M, G.Inc e v

mutual
  def WList.alternating (G : Graph α β) (M : Set β) : WList α β → Prop
    | nil x => ¬ IsMatching.VxMatched G M x
    | cons _u e w => e ∉ M ∧ WList.alternating' G M w

  def WList.alternating' (G : Graph α β) (M : Set β) : WList α β → Prop
    | nil _x => False
    | cons _u e w => e ∈ M ∧ WList.alternating G M w
end

structure IsAugmentingPath (G : Graph α β) {M : Set β} (hM : G.IsMatching M) (P : WList α β) :
    Prop extends G.IsPath P where
  last_unmatched : ∀ e ∈ M, ¬ G.Inc e P.last
  alternate : WList.alternating G M P

lemma IsMatching.augment_matching (G : Graph α β) {M : Set β} (hM : G.IsMatching M) {P : WList α β}
    (hP : G.IsAugmentingPath hM P) : G.IsMatching (M ∆ P.edgeSet) := by

  sorry

lemma IsMatching.augment_encard (G : Graph α β) {M : Set β} (hM : G.IsMatching M) {P : WList α β}
    (hP : G.IsAugmentingPath hM P) : (M ∆ P.edgeSet).encard = M.encard + 1 := by

  sorry

lemma IsMatching.maximal_iff_augmentingPath_empty (G : Graph α β) {M : Set β} (hM : G.IsMatching M) :
    Maximal (G.IsMatching) M ↔ ∀ P : WList α β, ¬ G.IsAugmentingPath hM P := by
  sorry

def IsVxCover (G : Graph α β) (X : Set α) : Prop :=
  ∀ e ∈ G.E, ∃ v ∈ X, G.Inc e v



theorem Konig_exist (G : Graph α β) [G.Finite] (hBip : G.Colorable 2) : ∃ (M : Set β) (X : Set α),
    G.IsMatching M ∧ G.IsVxCover X ∧ M.encard = X.encard := by
  obtain ⟨M, hMax⟩ := G.exists_maximal_isMatching

  sorry

end Graph
