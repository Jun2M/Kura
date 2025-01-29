import Kura.Graph.Remove


variable {V W E F : Type*} {G : Graph V E}

structure Subgraph (G : Graph V E) where
  Sᵥ : Set V := Set.univ
  Sₑ : Set E
  spec : ∀ e ∈ Sₑ, ∀ v ∈ G.inc e, v ∈ Sᵥ := by simp [Set.mem_univ]

namespace Subgraph

@[ext, simp]
lemma ext {S T : Subgraph G} (hS : S.Sᵥ = T.Sᵥ) (hT : S.Sₑ = T.Sₑ) : S = T := by
  cases S
  cases T
  simp only [mk.injEq]
  exact ⟨hS, hT⟩

@[coe]
def toGraph (S : Subgraph G) : Graph S.Sᵥ S.Sₑ where
  inc e := edge.pmap Subtype.mk (G.inc e) (S.spec e.val e.prop)

instance instCoeSubgraph (S : Subgraph G): CoeDep (Subgraph G) S (Graph S.Sᵥ S.Sₑ) where
  coe := S.toGraph

instance instLatticeSubgraph : Lattice (Subgraph G) where
  le S T := S.Sᵥ ⊆ T.Sᵥ ∧ S.Sₑ ⊆ T.Sₑ
  le_refl S := by simp only [subset_refl, and_self]
  le_trans S T U hST hTU := by
    obtain ⟨hSᵥ, hSₑ⟩ := hST
    obtain ⟨hTᵥ, hTₑ⟩ := hTU
    simp only [hSᵥ.trans hTᵥ, hSₑ.trans hTₑ, and_self]
  le_antisymm S T hST hTS := by
    obtain ⟨hSᵥ, hSₑ⟩ := hST
    obtain ⟨hTᵥ, hTₑ⟩ := hTS
    ext
    · refine ⟨(hSᵥ · ), (hTᵥ · )⟩
    · refine ⟨(hSₑ · ), (hTₑ · )⟩
  sup S T := by
    refine ⟨S.Sᵥ ∪ T.Sᵥ, S.Sₑ ∪ T.Sₑ, ?_⟩
    rintro e he v hv
    simp only [Set.mem_union] at he ⊢
    obtain heinS | heinT := he
    · left
      exact S.spec e heinS v hv
    · right
      exact T.spec e heinT v hv
  inf S T := by
    refine ⟨S.Sᵥ ∩ T.Sᵥ, S.Sₑ ∩ T.Sₑ, ?_⟩
    rintro e he v hv
    simp only [Set.mem_inter] at he ⊢
    obtain ⟨heinS, heinT⟩ := he
    exact ⟨S.spec e heinS v hv, T.spec e heinT v hv⟩
  le_sup_left S T := by simp only [not_and, Set.subset_union_left, and_self]
  le_sup_right S T := by simp only [not_and, Set.subset_union_right, and_self]
  sup_le S T U hSU hTU := by
    obtain ⟨hSᵥ, hSₑ⟩ := hSU
    obtain ⟨hTᵥ, hTₑ⟩ := hTU
    simp only [not_and, Set.union_subset_iff, hSᵥ, hTᵥ, and_self, hSₑ, hTₑ]
  inf_le_left S T := by simp only [not_and, Set.inter_subset_left, and_self]
  inf_le_right S T := by simp only [not_and, Set.inter_subset_right, and_self]
  le_inf S T U hSU hTU := by
    obtain ⟨hSᵥ, hSₑ⟩ := hSU
    obtain ⟨hTᵥ, hTₑ⟩ := hTU
    simp only [not_and, Set.subset_inter_iff, hSᵥ, hTᵥ, and_self, hSₑ, hTₑ]

/-- Complement in terms of edge set-/
instance instSubgraphCompl : HasCompl (Subgraph G) where
  compl S := ⟨G.incEsV S.Sₑᶜ , S.Sₑᶜ, (by
    rintro e he v hv
    simp only [Graph.incEsV, Set.mem_compl_iff, Set.mem_setOf_eq]
    use e, he)⟩

end Subgraph

-- def Separation (Sₑ : Set E) : Subgraph G × Subgraph G where
--   fst := ⟨G.incEsV Sₑ, Sₑ, G.incEsV_spec Sₑ⟩
--   snd := ⟨G.incEsV Sₑᶜ, Sₑᶜ, G.incEsV_spec Sₑᶜ⟩

structure Separation (G : Graph V E) where
  G₁ : Subgraph G
  G₂ : Subgraph G
  spec : G₁.Sₑ ∩ G₂.Sₑ = ∅

namespace Separation

noncomputable def order (Sep : Separation G) : ℕ := (Sep.G₁.Sᵥ ∩ Sep.G₂.Sᵥ).ncard



end Separation
