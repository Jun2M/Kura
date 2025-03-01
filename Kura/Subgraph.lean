import Kura.Basic


open Set Function
variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ G₁.Inc ≤ G₂.Inc
  le_refl G := by simp only [subset_refl, le_refl, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    simp only at h₁₂ h₂₃
    exact ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1, h₁₂.2.2.trans h₂₃.2.2⟩
  le_antisymm G₁ G₂ h₁₂ h₂₁ := by
    ext1
    · exact h₁₂.1.antisymm h₂₁.1
    · exact h₁₂.2.1.antisymm h₂₁.2.1
    · rw [h₁₂.2.2.antisymm h₂₁.2.2]

def induce (G : Graph α β) (U : Set α) : Graph α β where
  V := G.V ∩ U
  E := G.E ∩ {e | ∃ (he : e ∈ G.E), ∀ x ∈ G.toSym2 he, x ∈ U}
  Inc v e := G.Inc v e ∧ ∃ (he : e ∈ G.E), ∀ x ∈ G.toSym2 he, x ∈ U
  vx_mem_of_inc x y h := by
    obtain ⟨hinc, he, hx⟩ := h
    refine ⟨G.vx_mem_of_inc hinc, hx _ ?_⟩
    exact mem_toSym2_of_inc hinc
  edge_mem_of_inc v e h := by
    simp only [mem_inter_iff, mem_setOf_eq, and_exists_self]
    obtain ⟨he, hmem, hx⟩ := h
    exact ⟨hmem, hx⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    obtain ⟨he, _, h⟩ := he
    use v, hv, he
  not_hypergraph x y z e := by
    rintro ⟨hx, he, hx'⟩ ⟨hy, he', hy'⟩ ⟨hz, he'', hz'⟩
    obtain h | h | h := G.not_hypergraph hx hy hz <;>
    simp only [h, true_or, or_true]

lemma induce_le (G : Graph α β) (U : Set α) : G.induce U ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [induce, subset_inter_iff, inter_subset_left, true_and,
    Pi.le_def, le_Prop_eq, and_imp, forall_exists_index]
  rintro v e hinc hemem hvmem
  exact hinc

lemma induce_mono (G : Graph α β) (U V : Set α) (h : U ⊆ V) : G.induce U ≤ G.induce V := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [induce, subset_inter_iff, inter_subset_left, true_and]
    exact Subset.trans inter_subset_right h
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, subset_inter_iff, inter_subset_left,
    true_and]
    refine Subset.trans inter_subset_right ?_
    simp only [setOf_subset_setOf, and_imp]
    rintro e hemem hvmem
    use hemem
    exact fun x a ↦ h (hvmem x a)
  · simp only [induce, Pi.le_def, le_Prop_eq, and_imp, forall_exists_index]
    rintro v e hinc hemem hvmem
    use hinc, hemem
    exact fun x a ↦ h (hvmem x a)

lemma induce_induce_eq_induce_inter (G : Graph α β) (U V : Set α) :
    (G.induce U).induce V = G.induce (U ∩ V) := by
  ext1
  · simp only [induce, mem_inter_iff, mem_setOf_eq, and_exists_self]
    exact inter_assoc G.V U V
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff, mem_setOf_eq,
    and_self_left]
    ext e
    constructor
    · rintro ⟨⟨_, ⟨_, _⟩⟩, ⟨⟨he, hx⟩, hx''⟩⟩
      refine ⟨he, ⟨he, ?_⟩⟩
      rintro x hx'
      exact ⟨hx x hx', hx'' x hx' he hx⟩
    · rintro ⟨_, he, hx⟩
      simp only [mem_inter_iff, he, mem_setOf_eq, true_and, forall_const, and_self_left]
      refine ⟨fun x a ↦ mem_of_mem_inter_left (hx x a), ?_⟩
      rintro x hx' h
      exact mem_of_mem_inter_right (hx x hx')
  · rename_i v e
    simp only [induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff, mem_setOf_eq,
    and_self_left]
    constructor
    · rintro ⟨⟨hinc, he, hU⟩, ⟨_, b⟩⟩
      simp only [hinc, he, true_and]
      rintro x hx
      exact ⟨hU x hx, b x hx he hU⟩
    · rintro ⟨hinc, ⟨he, hUV⟩⟩
      refine ⟨⟨hinc, he, fun x a ↦ (hUV x a).1⟩, ⟨⟨he, fun x a ↦ (hUV x a).1⟩, ?_⟩⟩
      rintro x hinc he hU
      exact mem_of_mem_inter_right (hUV x hinc)

lemma induce_idem (G : Graph α β) (U : Set α) : (G.induce U).induce U = G.induce U := by
  convert G.induce_induce_eq_induce_inter U U
  simp only [inter_self]
def restrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := R ∩ G.E
  Inc v e := e ∈ R ∧ G.Inc v e
  vx_mem_of_inc _ _ h := G.vx_mem_of_inc h.2
  edge_mem_of_inc _ _ h := ⟨h.1, G.edge_mem_of_inc h.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.2
    exact ⟨v, he.1, hv⟩
  not_hypergraph _ _ _ _ hex hey hez := G.not_hypergraph hex.2 hey.2 hez.2

def edgeDel (G : Graph α β) (F : Set β) : Graph α β := G.restrict (G.E \ F)
