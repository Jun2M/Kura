import Kura.Comp.Color


open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph


structure IsMatching (G : Graph α β) (F : Set β) : Prop where
  supp : F ⊆ E(G)
  disj : ∀ v, ∀ e ∈ F, G.Inc e v → ∀ f ∈ F, G.Inc f v → e = f

structure IsPerfectMatching (G : Graph α β) (F : Set β) : Prop where
  supp : F ⊆ E(G)
  all_matched : ∀ v ∈ V(G), ∃! e ∈ F, G.Inc e v

lemma exists_isMatching (G : Graph α β) : ∃ M : Set β, G.IsMatching M :=
  ⟨∅, by constructor <;> simp [IsMatching]⟩

lemma exists_maximal_isMatching (G : Graph α β) [hE : Finite E(G)] :
    ∃ M : Set β, Maximal G.IsMatching M := by
  obtain ⟨M, hM⟩ := exists_isMatching G
  obtain ⟨M, _hM, hMax⟩ := Set.Finite.exists_le_maximal (s := {s : Set β | s ⊆ E(G) ∧ G.IsMatching s})
    (Finite.sep (Set.Finite.powerset hE) G.IsMatching) ⟨hM.supp, hM⟩
  simp only [mem_setOf_eq] at hMax
  rw [maximal_and_iff_left_of_imp (fun M hM ↦ hM.supp)] at hMax
  exact ⟨M, hMax.right⟩

lemma IsPerfectMatching_supported (G : Graph α β) (F : Set β) :
    G.IsPerfectMatching (E(G) ∩ F) ↔ G.IsPerfectMatching F := by
  sorry

def IsMatching.VxMatched (G : Graph α β) (M : Set β) (v : α) : Prop :=
  ∃ e ∈ M, G.Inc e v

end Graph

def WList.alt (G : Graph α β) (M : Set β) : WList α β → Prop
  | nil _x => False
  | cons _u _e (nil _) => True
  | cons _u e (cons _v f w) => (e ∉ M ↔ f ∈ M) ∧ WList.alt G M w

namespace Graph

structure IsAlternatingPath (G : Graph α β) {M : Set β} (hM : G.IsMatching M) (P : WList α β) :
    Prop extends G.IsPath P where
  first_unmatched : ∀ e ∈ M, ¬ G.Inc e P.first
  alternate : WList.alt G M P

structure IsAugmentingPath (G : Graph α β) {M : Set β} (hM : G.IsMatching M) (P : WList α β) :
    Prop extends G.IsAlternatingPath hM P where
  last_unmatched : ∀ e ∈ M, ¬ G.Inc e P.last


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
  ∀ e ∈ E(G), ∃ v ∈ X, G.Inc e v

lemma foo (G : Graph α β) [G.Bipartite] {M : Set β} (hM : G.IsMatching M) (he : e ∈ E(G))
    (h : ∀ e ∈ M, ¬ G.Inc e (G.zeroVx he)) : ∃ e ∈ M, G.Inc e (G.oneVx he) := by
  sorry

lemma foo2 (G : Graph α β) [G.Bipartite] (hinc : G.Inc e v) (hv0 : G.color v = 0) :
    G.zeroVx hinc.edge_mem = v := by
  sorry

lemma foo3 (G : Graph α β) [G.Bipartite] (hinc : G.Inc e v) (hv0 : G.color v = 1) :
    G.oneVx hinc.edge_mem = v := by
  sorry

theorem Konig_exist (G : Graph α β) [Finite V(G)] [Finite E(G)] [G.Bipartite] :
    ∃ (M : Set β) (X : Set α), G.IsMatching M ∧ G.IsVxCover X ∧ M.ncard = X.ncard := by
  classical
  obtain ⟨M, hMatching, hle⟩ := G.exists_maximal_isMatching
  let f : E(G) → α := fun e ↦ if ∃ P : WList α β, G.IsAlternatingPath hMatching P ∧ P.last = G.oneVx e.prop
    then G.oneVx e.prop else G.zeroVx e.prop
  let M' : Set E(G) := sorry
  have hM' : (Subtype.val '' M') = M := by sorry
  let X := f '' M'

  use M, X, hMatching, ?_
  · -- M and X has the same size as f is injective
    unfold X
    rw [Set.ncard_image_of_injOn (f := f) ?_, ← hM', Set.ncard_image_of_injective _ Subtype.val_injective]
    rintro ⟨a, ha⟩ haM' ⟨b, hb⟩ hbM' heq
    sorry
  -- Hence, suffices to show that X is a vertex cover
  rintro e he
  -- If the 0-vertex of e is in X, e is covered by X.
  by_cases h0X : G.zeroVx he ∈ X
  · exact ⟨G.zeroVx he, h0X, G.isLink_zeroVx_oneVx he |>.inc_left⟩
  -- Otherwise, e must be covered by X by 1-vertex of e.
  refine ⟨G.oneVx he, ?_, (G.isLink_zeroVx_oneVx he |>.inc_right)⟩
  simp only [mem_image, Subtype.exists, X, f]
  -- If 0-vertex of e is not matched, then e is an alternating path.
  obtain h0notmatched | ⟨e', he'M, he'inc⟩ := (em (∃ e' ∈ M, G.Inc e' (G.zeroVx he))).symm
  · push_neg at h0notmatched
    obtain ⟨e', he'M, he'inc⟩ : ∃ e' ∈ M, G.Inc e' (G.oneVx he) := foo G hMatching he h0notmatched
    have := G.foo3 he'inc (by simp)
    use e', hMatching.supp he'M, sorry -- M and M'
    have hP : ∃ P, G.IsAlternatingPath hMatching P ∧ P.last = G.oneVx (hMatching.supp he'M) := by
      let P := WList.cons (G.zeroVx he) e' (WList.nil (G.oneVx he))
      use P, ⟨(sorry : G.IsPath P), h0notmatched, ?_⟩, by simp [P, this]
      reduce
      trivial
    simpa only [hP, ↓reduceIte, f, X]
  -- Otherwise, 0-vertex of e is matched by some e' ∈ M.
  use e', hMatching.supp he'M, sorry -- M and M'
  have h0e' : G.zeroVx he = G.zeroVx (hMatching.supp he'M) := (G.foo2 he'inc (by simp)).symm
  -- Since 0-vertex of e' = 0-vertex of e is not in X, 1-vertex of e' must be in X.
  obtain hP | hP := (em (∃ P : WList α β, G.IsAlternatingPath hMatching P ∧ P.last = G.oneVx (hMatching.supp he'M))).symm
  · exfalso
    apply h0X
    rw [h0e']
    simp only [mem_image, Subtype.exists, X, f]
    use e', hMatching.supp he'M, sorry, by simp only [hP, ↓reduceIte, X, f] -- M and M'
  -- Then, there is an alternating path that ends at 1-vertex of e'.
  simp only [hP, ↓reduceIte]
  obtain ⟨P, hP, hPlast⟩ := hP
  -- If 1-vertex of e is in the alternating path, stopping at it give an augmenting path.
  by_cases h1eP : G.oneVx he ∈ V(P)
  · sorry
  -- Otherwise, extend the alternating path by e', then e to finish at 1-vertex of e.
  sorry


end Graph
