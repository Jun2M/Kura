import Kura.Comp.Color


open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph


structure IsMatching (G : Graph α β) (F : Set β) : Prop where
  supp : F ⊆ E(G)
  disj : ∀ e ∈ F, ∀ f ∈ F, e ≠ f → Disjoint (G.toMultiset e) (G.toMultiset f)

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
  ∀ e ∈ E(G), ∃ v ∈ X, G.Inc e v



theorem Konig_exist (G : Graph α β) [G.Finite] (hBip : G.Colorable 2) : ∃ (M : Set β) (X : Set α),
    G.IsMatching M ∧ G.IsVxCover X ∧ M.encard = X.encard := by
  obtain ⟨M, hMax⟩ := G.exists_maximal_isMatching

  sorry

end Graph
