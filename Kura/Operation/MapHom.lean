import Kura.Operation.Map
import Kura.Operation.Hom

open Set Function
variable {α β α' β' γ δ ε ζ : Type*} {G G' G₁ G₁' H : Graph α β} {G₂ G₂' : Graph γ δ}
  {G₃ G₃' : Graph ε ζ} {a b c : α} {e f : β} {u v w : γ} {x y z : δ} {S S' T T' U U': Set α}
  {F F' R R' : Set β}
namespace Graph


lemma vxMap.IsHomOn (φ : α → α') : (HomSys.ofVxFun φ).IsHomOn G (vxMap G φ) where
  Mapsto_vx v hv := by
    simp only [V, HomSys.ofVxFun, mem_image]
    use v
  inc₂ ⦃e x y⦄ h := by
    rw [vxMap_inc₂_toMultiset]
    simp [toMultiset_eq_pair_iff.mpr h]

lemma vxMap.HasHom (φ : α → α') : G ≤→ (vxMap G φ) :=
  ⟨HomSys.ofVxFun φ, vxMap.IsHomOn φ⟩

lemma vxMap.IsIsomOn (φ : α → α') (hφ : InjOn φ G.V) :
    (HomSys.ofVxFun φ).IsIsomOn G (vxMap G φ) where
  toIsHomOn := vxMap.IsHomOn φ
  bijOn_vx := ⟨mapsTo'.mpr fun ⦃a⦄ a ↦ a, hφ, fun ⦃a⦄ a ↦ a⟩
  bijOn_edge := by
    refine ⟨fun e he ↦ ?_, fun e₁ he₁ e₂ he₂ heq ↦ ?_, fun e he ↦ ?_⟩
    · simpa only [vxMap_edgeSet, HomSys.ofVxFun_edgeFun, id_eq]
    · simpa only using heq
    · simpa only [HomSys.ofVxFun, id_eq, image_id', vxMap_edgeSet] using he

lemma vxMap.HasIsom (φ : α → α') (hφ : InjOn φ G.V) : G ≤↔ (vxMap G φ) :=
  ⟨HomSys.ofVxFun φ, vxMap.IsIsomOn φ hφ⟩



def edgePreimg.HomSys (σ : β' → β) : HomSys α β' α β where
  toFun := id
  edgeFun := σ

lemma edgePreimg.HomSys.IsHomOn (σ : β' → β) : (edgePreimg.HomSys σ).IsHomOn (edgePreimg G σ) G where
  Mapsto_vx v hv := by simpa only [HomSys, id_eq] using hv
  inc₂ ⦃e x y⦄ h := by simpa only [HomSys, id_eq, Inc₂, exists_eq_left'] using h

lemma edgePreimg.HasHom (σ : β' → β) : (edgePreimg G σ) ≤→ G :=
  ⟨edgePreimg.HomSys σ, edgePreimg.HomSys.IsHomOn σ⟩

-- TODO: Have some more think about what the appropriate assumptions should be.
-- lemma edgePreimg.HomSys.IsIsomOn (σ : β' → β) (hσ : BijOn σ univ G.E) :
--     (edgePreimg.HomSys σ).IsIsomOn (edgePreimg G σ) G where
--   toIsHomOn := edgePreimg.HomSys.IsHomOn σ
--   bijOn_vx := by
--     refine ⟨fun v hv ↦ ?_, fun u hu v hv heq ↦ ?_, fun v hv ↦ ?_⟩
--     · simpa only [HomSys, id_eq, edgePreimg, oftoMultiset_V] using hv
--     · simpa only [HomSys, id_eq] using heq
--     · simpa only [HomSys, id_eq, image_id', edgePreimg, oftoMultiset_V] using hv
--   bijOn_edge := by
--     refine ⟨fun e he ↦ ?_, fun e₁ he₁ e₂ he₂ heq ↦ ?_, fun e he ↦ ?_⟩
--     · simpa only [HomSys, edgePreimg, oftoMultiset_E, toMultiset_card_eq_two_iff,
--       mem_setOf_eq] using he
--     · simpa? [edgePreimg, E, HomSys, id_eq] using heq
--     · simpa? [edgePreimg, E, HomSys, id_eq] using he


noncomputable def edgePreimg.HomSys' [h : Nonempty β'] (σ : β' → β) : Graph.HomSys α β α β' where
  toFun := id
  edgeFun e :=
    haveI : Decidable (∃ e', σ e' = e) := Classical.dec _
    if hex : ∃ e', σ e' = e then hex.choose else h.some

lemma edgePreimg.HomSys.IsEmbOn [h : Nonempty β'] (σ : β' → β) (hσ : SurjOn σ univ G.E) :
    (edgePreimg.HomSys' σ).IsEmbOn G (edgePreimg G σ) where
  Mapsto_vx v hv := by simpa only [V, HomSys', id_eq] using hv
  inc₂ ⦃e x y⦄ hbtw := by
    simp only [HomSys', id_eq, Inc₂, exists_eq_left']
    have hex : ∃ e', σ e' = e := by
      obtain ⟨e', he', rfl⟩ := hσ hbtw.edge_mem
      use e'
    simp only [hex, ↓reduceDIte]
    rwa [hex.choose_spec]
  injOn_vx u hu v hv heq := by simpa only [HomSys, id_eq] using heq
  injOn_edge e₁ he₁ e₂ he₂ heq := by
    have hex₁ : ∃ e₁', σ e₁' = e₁ := by
      obtain ⟨e', he', rfl⟩ := hσ he₁
      use e'
    have hex₂ : ∃ e₂', σ e₂' = e₂ := by
      obtain ⟨e', he', rfl⟩ := hσ he₂
      use e'
    simp only [HomSys', hex₁, ↓reduceDIte, hex₂] at heq
    change hex₁.choose = hex₂.choose at heq
    rw [← hex₁.choose_spec, ← hex₂.choose_spec, heq]

lemma edgePreimg.HasEmb [Nonempty β'] (σ : β' → β) (hσ : SurjOn σ univ G.E) :
    G ≤↪ (edgePreimg G σ) := ⟨edgePreimg.HomSys' σ, edgePreimg.HomSys.IsEmbOn σ hσ⟩
