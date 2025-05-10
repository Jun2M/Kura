import Kura.Constructor
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2

variable {α ε : Type*} {x y z u v w : α} {e f : ε} {G H : Graph α ε} {F F₁ F₂ : Set ε} {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

structure IsSubgraph (H G : Graph α ε) : Prop where
  vx_subset : H.V ⊆ G.V
  inc₂_of_inc₂ : ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y

def inf (G H : Graph α ε) : Graph α ε := Graph.mk' (G.V ∩ H.V)
  (fun e x y ↦ G.Inc₂ e x y ∧ H.Inc₂ e x y)
  (fun _ _ _ ⟨hxy1, hxy2⟩ ↦ ⟨hxy1.symm, hxy2.symm⟩)
  (fun _ _ _ _ _ ⟨hxy1, _⟩ ⟨huv1, _⟩ ↦ hxy1.left_eq_or_eq_of_inc₂ huv1)
  (fun _ _ _ ⟨hxy1, hxy2⟩ ↦ ⟨hxy1.vx_mem_left, hxy2.vx_mem_left⟩)

/-- The subgraph order -/
instance : SemilatticeInf (Graph α ε) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.le, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.inc₂_of_inc₂ a, fun a ↦ h₂.inc₂_of_inc₂ a⟩
  inf := inf
  inf_le_left G H := ⟨inter_subset_left, fun e x y h ↦ h.1⟩
  inf_le_right G H := ⟨inter_subset_right, fun e x y h ↦ h.2⟩
  le_inf _ _ _ h₁ h₂ := ⟨subset_inter h₁.1 h₂.1, fun e x y ↦ imp_and.mpr ⟨(h₁.2 ·), (h₂.2 ·)⟩⟩

lemma Inc₂.of_le (h : H.Inc₂ e x y) (hle : H ≤ G) : G.Inc₂ e x y :=
  hle.2 h

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vxSet_subset_of_le (h : H ≤ G) : H.V ⊆ G.V :=
  h.1

lemma edgeSet_subset_of_le (h : H ≤ G) : H.E ⊆ G.E := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_inc₂_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (H.V ⊆ G.V) ∧ ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma Inc₂.of_le_of_mem (h : G.Inc₂ e x y) (hle : H ≤ G) (he : e ∈ H.E) : H.Inc₂ e x y := by
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq_of_inc₂ h
  · assumption
  exact huv.symm

lemma inc₂_iff_inc₂_of_le_of_mem (hle : H ≤ G) (he : e ∈ H.E) :
    G.Inc₂ e x y ↔ H.Inc₂ e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

lemma inc_iff_inc_of_le_of_mem (hle : G ≤ H) (he : e ∈ G.E) : G.Inc e x ↔ H.Inc e x := by
  revert x
  simp [inc_iff_inc_iff, inc₂_iff_inc₂_of_le_of_mem hle he]

lemma le_iff_inc : G ≤ H ↔ G.V ⊆ H.V ∧ G.E ⊆ H.E ∧ ∀ e ∈ G.E, ∀ v,
  G.Inc e v ↔ H.Inc e v := by
  constructor
  · rintro hle
    refine ⟨vxSet_subset_of_le hle, edgeSet_subset_of_le hle, fun e he v ↦ ?_⟩
    rw [inc_iff_inc_of_le_of_mem hle he]
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, fun e x y ↦ ?_⟩
    by_cases he : e ∈ G.E
    · rw [inc_eq_inc_iff.mp (by ext; exact hinc e he _)]
      exact id
    · simp [he]

lemma toMultiset_eq_of_le (hle : H ≤ G) (he : e ∈ H.E) : H.toMultiset e = G.toMultiset e := by
  obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet he
  rw [toMultiset_eq_pair_iff.mpr h, toMultiset_eq_pair_iff.mpr (h.of_le hle)]

lemma toSym2_eq_of_le (hle : H ≤ G) (he : e ∈ H.E) :
    H.toSym2 e he = G.toSym2 e (edgeSet_subset_of_le hle he) := by
  obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet he
  rw [(toSym2_eq_pair_iff he).mpr h,
    (toSym2_eq_pair_iff (edgeSet_subset_of_le hle he)).mpr (h.of_le hle)]

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α ε} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : H₁.V ⊆ H₂.V)
    (hE : H₁.E ⊆ H₂.E) : H₁ ≤ H₂ where
  vx_subset := hV
  inc₂_of_inc₂ e x y h := by
    rw [← G.inc₂_iff_inc₂_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α ε} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : H₁.V = H₂.V)
    (hE : H₁.E = H₂.E) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

/-- Restrict `G : Graph α ε` to the edges in a set `E₀` without removing vertices -/
@[simps]
def edgeRestrict (G : Graph α ε) (E₀ : Set ε) : Graph α ε where
  V := G.V
  E := E₀ ∩ G.E
  Inc₂ e x y := e ∈ E₀ ∧ G.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := ⟨fun h ↦ by simp [h, G.exists_inc₂_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_inc₂ _ _ _ h := h.2.vx_mem_left

scoped infixl:65 " ↾ "  => Graph.edgeRestrict

lemma Inc₂.edgeRestrict (hG : G.Inc₂ e x y) (he : e ∈ F) : (G ↾ F).Inc₂ e x y := by
  rw [edgeRestrict_inc₂]
  exact ⟨he, hG⟩

lemma Inc₂.of_edgeRestrict (hG : (G ↾ F).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [edgeRestrict_inc₂] at hG
  exact hG.2

@[simp]
lemma edgeRestrict_inc : (G ↾ F).Inc e x ↔ e ∈ F ∧ G.Inc e x := by
  simp_rw [inc_iff_exists_inc₂, edgeRestrict_inc₂, exists_and_left]

@[simp]
lemma edgeRestrict_le {E₀ : Set ε} : G ↾ E₀ ≤ G where
  vx_subset := rfl.le
  inc₂_of_inc₂ := by simp

lemma edgeRestrict_mono_right (G : Graph α ε) {F₀ F : Set ε} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vx_subset := rfl.subset
  inc₂_of_inc₂ _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set ε) : H ↾ F ≤ G ↾ F :=
  G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vxSet_subset_of_le h)
    (by simp [inter_subset_right.trans (edgeSet_subset_of_le h)])

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α ε) (F : Set ε) : G ↾ (F ∩ G.E) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α ε) (F : Set ε) : G ↾ (G.E ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_eq_self_iff (G : Graph α ε) (F : Set ε) : G ↾ F = G ↔ G.E ⊆ F := by
  constructor <;> intro h
  · rw [← h]
    simp [edgeRestrict_edgeSet, inter_subset_left]
  · refine le_antisymm edgeRestrict_le ?_
    rw [ext_of_le_le edgeRestrict_le le_rfl rfl]
    exact inter_eq_right.mpr h

@[simp]
lemma edgeRestrict_self (G : Graph α ε) : G ↾ G.E = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α ε) (hF : G.E ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α ε) (F₁ F₂ : Set ε) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le (edgeRestrict_le.trans (by simp)) (by simp) (by simp) ?_
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma edgeRestrict_le_edgeRestrict_iff (G : Graph α ε) (F₁ F₂ : Set ε) :
    G ↾ F₁ ≤ G ↾ F₂ ↔ F₁ ∩ G.E ⊆ F₂ ∩ G.E := by
  refine ⟨fun h e he ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_inter_iff] at he ⊢
    simp [he, (edgeSet_subset_of_le h he).1]
  · refine ⟨subset_rfl, fun e x y hbtw ↦ ?_⟩
    rw [edgeRestrict_inc₂] at hbtw ⊢
    exact ⟨(h ⟨hbtw.1, hbtw.2.edge_mem⟩).1, hbtw.2⟩

@[simp]
lemma edgeRestrict_eq_edgeRestrict_iff (G : Graph α ε) (F₁ F₂ : Set ε) :
    G ↾ F₁ = G ↾ F₂ ↔ F₁ ∩ G.E = F₂ ∩ G.E := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeRestrict_le_edgeRestrict_iff, edgeRestrict_le_edgeRestrict_iff]

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`, but we also
use `copy` for better definitional properties. -/
@[simps!]
def edgeDelete (G : Graph α ε) (F : Set ε) : Graph α ε :=
  (G.edgeRestrict (G.E \ F)).copy (E := G.E \ F) (Inc₂ := fun e x y ↦ e ∉ F ∧ G.Inc₂ e x y) rfl
    (by simp [diff_subset])
    (fun e x y ↦ by
      simp only [edgeRestrict_inc₂, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
      exact fun h _ ↦ h.edge_mem)

scoped infixl:65 " ＼ " => Graph.edgeDelete

@[simp]
lemma edgeDelete_edgeSet_subset (G : Graph α ε) (F : Set ε) : (G ＼ F).E ⊆ G.E := by
  simp [edgeDelete_edgeSet]
  exact diff_subset

@[simp]
lemma edgeDelete_edgeSet_ncard_le (G : Graph α ε) (F : Set ε) [Finite G.E] :
    (G ＼ F).E.ncard ≤ G.E.ncard := ncard_le_ncard <| G.edgeDelete_edgeSet_subset F

@[simp↓]
lemma edgeDelete_edgeSet_ncard_lt_iff (G : Graph α ε) (F : Set ε) [Finite G.E] :
    (G ＼ F).E.ncard < G.E.ncard ↔ (G.E ∩ F).Nonempty := by
  rw [edgeDelete_edgeSet]
  refine ⟨fun h ↦ ?_, fun h ↦ ncard_lt_ncard <| diff_ssubset_left_iff.mpr h⟩
  by_contra! h'
  rw [← disjoint_iff_inter_eq_empty] at h'
  simp only [h'.sdiff_eq_left, lt_self_iff_false] at h

@[simp↓]
lemma edgeDelete_singleton_edgeSet_ncard_lt_iff (G : Graph α ε) (e : ε) [Finite G.E] :
    (G ＼ {e}).E.ncard < G.E.ncard ↔ e ∈ G.E := by
  simp only [edgeDelete_edgeSet_ncard_lt_iff, inter_singleton_nonempty]

lemma Inc₂.edgeDelete (hG : G.Inc₂ e x y) (he : e ∉ F) : (G ＼ F).Inc₂ e x y := by
  rw [edgeDelete_inc₂]
  exact ⟨he, hG⟩

lemma Inc₂.of_edgeDelete (hG : (G ＼ F).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [edgeDelete_inc₂] at hG
  exact hG.2

@[simp]
lemma edgeDelete_inc : (G ＼ F).Inc e x ↔ e ∉ F ∧ G.Inc e x := by
  simp_rw [inc_iff_exists_inc₂, edgeDelete_inc₂, exists_and_left]

lemma edgeDelete_eq_edgeRestrict (G : Graph α ε) (F : Set ε) :
    G ＼ F = G ↾ (G.E \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

lemma edgeDelete_anti_right (G : Graph α ε) {F₀ F : Set ε} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (H.E \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_subset_of_le h)

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α ε) (F₁ F₂ : Set ε) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α ε) (F₁ F₂ : Set ε) : G ↾ F₁ ＼ F₂ = G ↾ (F₁ \ F₂) := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

@[simp]
lemma edgeDelete_eq_self_iff (G : Graph α ε) (F : Set ε) : G ＼ F = G ↔ Disjoint G.E F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_eq_self_iff, ← Set.subset_compl_iff_disjoint_right,
    diff_eq_compl_inter]
  simp only [subset_inter_iff, subset_refl, and_true]

lemma edgeDelete_eq_self (G : Graph α ε) (hF : Disjoint G.E F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

@[simp]
lemma edgeDelete_le_edgeDelete (G : Graph α ε) (F₁ F₂ : Set ε) :
    G ＼ F₁ ≤ G ＼ F₂ ↔ G.E \ F₁ ⊆ G.E \ F₂ := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, edgeRestrict_le_edgeRestrict_iff,
    inter_eq_left.mpr diff_subset, inter_eq_left.mpr diff_subset]

@[simp]
lemma edgeDelete_eq_edgeDelete_iff (G : Graph α ε) (F₁ F₂ : Set ε) :
    G ＼ F₁ = G ＼ F₂ ↔ G.E \ F₁ = G.E \ F₂ := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeDelete_le_edgeDelete, edgeDelete_le_edgeDelete]

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V ε ≤ G ↔ V ⊆ G.V := by
  simp [le_iff]

lemma edgeDelete_eq_noEdge (G : Graph α ε) (hF : G.E ⊆ F) : G ＼ F = Graph.noEdge G.V ε := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_inc₂, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
    not_inc₂_of_not_mem_edgeSet, iff_false, not_and]
  exact fun h hbtw ↦ h (hF hbtw.edge_mem)

instance instOrderBotGraph : OrderBot (Graph α ε) where
  bot := Graph.noEdge ∅ ε
  bot_le G := by
    rw [le_iff_inc]
    refine ⟨?_, ?_⟩ <;> simp [Graph.noEdge, empty_subset, mem_empty_iff_false,
    false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α ε) where
  default := ⊥

@[simp] lemma bot_V : (⊥ : Graph α ε).V = ∅ := rfl

@[simp] lemma bot_E : (⊥ : Graph α ε).E = ∅ := rfl

instance instVxSetIsEmptyBot : IsEmpty (⊥ : Graph α ε).V := by
  simp

instance instESetIsEmptyBot : IsEmpty (⊥ : Graph α ε).E := by
  simp

@[simp]
lemma vxSet_empty_iff_eq_bot : G.V = ∅ ↔ G = ⊥ := by
  constructor <;> rintro h
  · apply ext_inc h ?_
    simp only [bot_E, mem_empty_iff_false, not_false_eq_true, not_inc_of_not_mem_edgeSet, iff_false]
    rintro e v hinc
    have := h ▸ hinc.vx_mem
    simp only [mem_empty_iff_false] at this
  · rw [h]
    rfl

instance instUniqueGraph [IsEmpty α] : Unique (Graph α ε) where
  default := ⊥
  uniq G := by
    rw [← vxSet_empty_iff_eq_bot]
    exact eq_empty_of_isEmpty G.V

@[simp] lemma eq_bot_of_isEmpty [IsEmpty α] : G = ⊥ := instUniqueGraph.uniq G

@[simp]
lemma edgeDelete_empty : G ＼ (∅ : Set ε) = G := by
  simp

@[simp]
lemma edgeDelete_edgeSet_eq_bot : (G ＼ G.E) = Graph.noEdge G.V ε := by
  simp only [subset_refl, edgeDelete_eq_noEdge]

@[simp]
lemma edgeDelete_univ : G ＼ (univ : Set ε) = Graph.noEdge G.V ε := by
  simp [edgeDelete_eq_noEdge]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `G.V` for this definition to work,
even though this is the standard use case) -/
@[simps! vxSet inc₂]
protected def induce (G : Graph α ε) (X : Set α) : Graph α ε := Graph.mk'
  (V := X)
  (Inc₂ := fun e x y ↦ G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X)
  (inc₂_symm := fun e x y ↦ by simp [G.inc₂_comm, and_comm (a := (x ∈ X))])
  (eq_or_eq_of_inc₂_of_inc₂ := fun e x y u v ⟨h, _⟩ ⟨h', _⟩ ↦ G.eq_or_eq_of_inc₂_of_inc₂ h h')
  (vx_mem_left_of_inc₂ := fun _ _ _ ⟨_, h⟩ ↦ h.1)

notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ G.V) : G[X] ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

lemma Inc₂.induce (hG : G.Inc₂ e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Inc₂ e x y := by
  rw [induce_inc₂]
  exact ⟨hG, hx, hy⟩

lemma Inc₂.of_induce (hG : G[X].Inc₂ e x y) : G.Inc₂ e x y := by
  rw [induce_inc₂] at hG
  exact hG.1

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α ε) (X : Set α) :
    (G.induce X).E = {e | ∃ x y, G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α ε) (X : Set α) :
    (G.induce X).E ⊆ G.E := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma Inc₂.mem_induce_iff {X : Set α} (hG : G.Inc₂ e x y) : e ∈ G[X].E ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq_of_inc₂ he <;> simp [hx', hy']

lemma induce_induce (G : Graph α ε) (X Y : Set α) : G[X][Y] = G[Y] ↾ G[X].E := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_inc₂, edgeRestrict_inc₂]
  obtain he | he := em' (G.Inc₂ e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

lemma induce_mono (hle : H ≤ G) (hsu : X ⊆ Y) : H[X] ≤ G[Y] := by
  rw [le_iff]
  refine ⟨hsu, fun e x y ↦ ?_⟩
  rw [induce_inc₂, induce_inc₂]
  exact fun ⟨hbtw, hxU, hyU⟩ ↦ ⟨hbtw.of_le hle, hsu hxU, hsu hyU⟩

lemma induce_mono_left (hle : H ≤ G) (X : Set α) : H[X] ≤ G[X] :=
  induce_mono hle subset_rfl

lemma induce_mono_right (G : Graph α ε) (hXY : X ⊆ Y) : G[X] ≤ G[Y] :=
  induce_mono (le_refl G) hXY

@[simp]
lemma induce_le_induce_iff (G : Graph α ε) (X Y : Set α) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨vxSet_subset_of_le, induce_mono_right G⟩

@[simp]
lemma induce_eq_induce_iff (G : Graph α ε) (X Y : Set α) : G[X] = G[Y] ↔ X = Y := by
  rw [le_antisymm_iff, induce_le_induce_iff, induce_le_induce_iff, antisymm_iff]

@[simp]
lemma induce_eq_self_iff (G : Graph α ε) (X : Set α) : G[X] = G ↔ X = G.V := by
  constructor <;> intro h
  · rw [← h]
    rfl
  · simp only [le_antisymm_iff, induce_le h.le, true_and]
    subst X
    rw [le_iff]
    refine ⟨subset_refl _, fun e x y hbtw ↦ ?_⟩
    rw [induce_inc₂]
    exact ⟨hbtw, hbtw.vx_mem_left, hbtw.vx_mem_right⟩

@[simp]
lemma induce_empty : G[∅] = ⊥ := by
  rw [← vxSet_empty_iff_eq_bot]
  rfl

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vxDelete (G : Graph α ε) (X : Set α) : Graph α ε := G [G.V \ X]

instance instHSub : HSub (Graph α ε) (Set α) (Graph α ε) where
  hSub := Graph.vxDelete

lemma vxDelete_def (G : Graph α ε) (X : Set α) : G - X = G [G.V \ X] := rfl

@[simp]
lemma vxDelete_vxSet (G : Graph α ε) (X : Set α) : (G - X).V = G.V \ X := rfl

@[simp]
lemma vxDelete_edgeSet (G : Graph α ε) (X : Set α) :
  (G - X).E = {e | ∃ x y, G.Inc₂ e x y ∧ (x ∈ G.V ∧ x ∉ X) ∧ y ∈ G.V ∧ y ∉ X}  := rfl

@[simp]
lemma vxDelete_inc₂ (G : Graph α ε) (X : Set α) :
    (G - X).Inc₂ e x y ↔ (G.Inc₂ e x y ∧ (x ∈ G.V ∧ x ∉ X) ∧ y ∈ G.V ∧ y ∉ X) := Iff.rfl

@[simp]
lemma vxDelete_le : G - X ≤ G :=
  G.induce_le diff_subset

lemma Inc₂.mem_vxDelete_iff {X : Set α} (hG : G.Inc₂ e x y) : e ∈ (G - X).E ↔ x ∉ X ∧ y ∉ X := by
  rw [vxDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.vx_mem_left,
    and_iff_right hG.vx_mem_right]

@[simp]
theorem vxDelete_eq_self_iff : G - X = G ↔ Disjoint X G.V := by
  simp only [vxDelete_def, induce_eq_self_iff, sdiff_eq_left, disjoint_comm]

lemma vxDelete_mono_left (hle : G ≤ H) : G - X ≤ H - X := by
  simp [vxDelete_def]
  exact induce_mono hle (diff_subset_diff_left <| vxSet_subset_of_le hle)

lemma vxDelete_anti_right (hsu : Y ⊆ X) : G - X ≤ G - Y := by
  simp only [vxDelete_def, induce_le_induce_iff]
  exact diff_subset_diff_right hsu

@[simp]
lemma vxDelete_le_vxDelete_iff : G - X ≤ G - Y ↔ G.V \ X ⊆ G.V \ Y := by
  simp_rw [vxDelete_def, induce_le_induce_iff]

@[simp]
lemma vxDelete_eq_vxDelete_iff : G - X = G - Y ↔ G.V \ X = G.V \ Y := by
  simp_rw [vxDelete_def, induce_eq_induce_iff]

@[simp]
lemma vxDelete_empty : G - (∅ : Set α) = G := by
  simp [vxDelete_def]

@[simp]
lemma vxDelete_V : G - (G.V : Set α) = ⊥ := by
  simp [vxDelete_def]

@[simp]
lemma vxDelete_univ : G - (univ : Set α) = ⊥ := by
  simp [vxDelete_def]

-- TODO: prove some lemmas about `G - X`

@[simp]
lemma edgeRestrict_induce (G : Graph α ε) (X : Set α) (F : Set ε) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_inc₂, edgeRestrict_inc₂]
  tauto

lemma edgeRestrict_vxDelete (G : Graph α ε) (F : Set ε) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vxDelete_inc₂, edgeRestrict_inc₂, edgeRestrict_vxSet]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α ε) (X : Set α) (F : Set ε) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vxDelete (G : Graph α ε) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by simp +contextual

@[simp]
lemma vxDelete_induce (G : Graph α ε) (X D : Set α) : (G - D)[X] = G[X] ↾ (G - D).E :=
  induce_induce G (G.V \ D) X

@[simp]
lemma vxDelete_vxDelete : G - X - Y = G - (X ∪ Y) := by
  rw [G.vxDelete_def, induce_vxDelete, diff_diff]
  rfl

@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.Inc₂ e u v := by
  simp only [le_iff, singleEdge_vxSet, Set.pair_subset_iff, singleEdge_inc₂_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.vx_mem_left, h.vx_mem_right⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α ε) : Prop := ∀ ⦃e⦄, e ∈ G.E → e ∈ H.E → G.Inc₂ e = H.Inc₂ e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α ε} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [← inc₂_iff_inc₂_of_le_of_mem h₁ he₁, ← inc₂_iff_inc₂_of_le_of_mem h₂ he₂]

lemma compatible_self (G : Graph α ε) : G.Compatible G := by
  simp [Compatible]

lemma compatible_iff_inter_edge_eq_inter : G.Compatible H ↔ (G ⊓ H).E = G.E ∩ H.E := by
  constructor
  · rintro h
    ext e
    simp only [mem_setOf_eq, mem_inter_iff]
    refine ⟨fun ⟨x, y, hG, hH⟩ ↦ ⟨hG.edge_mem, hH.edge_mem⟩, fun ⟨heG, heH⟩ ↦ ?_⟩
    · obtain ⟨x, y, hbtw⟩ := exists_inc₂_of_mem_edgeSet heG
      exact ⟨x, y, hbtw, (h heG heH) ▸ hbtw⟩
  · rintro h e heG heH
    have : e ∈ G.E ∩ H.E := ⟨heG, heH⟩
    obtain ⟨u, v, hbtwG, hbtwH⟩ := h ▸ this
    rw [← toSym2_eq_pair_iff (by assumption)] at hbtwG hbtwH
    rw [← toSym2_eq_toSym2_iff heG heH, hbtwG, hbtwH]

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α ε) : Graph α ε where
  V := G.V ∪ H.V
  E := G.E ∪ H.E
  Inc₂ e x y := G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y)
  inc₂_symm e x y h := by rwa [G.inc₂_comm, H.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_eq_or_eq_of_inc₂ h'
    · exact False.elim <| h'.1 h.edge_mem
    · exact False.elim <| h.1 h'.edge_mem
    exact h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨?_, fun ⟨x, y, h⟩ ↦ h.elim (fun h' ↦ .inl h'.edge_mem) (fun h' ↦ .inr h'.2.edge_mem)⟩
    rw [← Set.union_diff_self]
    rintro (he | ⟨heH, heG⟩)
    · obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet he
      exact ⟨x, y, .inl h⟩
    obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet heH
    exact ⟨x, y, .inr ⟨heG, h⟩⟩
  vx_mem_left_of_inc₂ := by
    rintro e x y (h | h)
    · exact .inl h.vx_mem_left
    exact .inr h.2.vx_mem_left

instance : Union (Graph α ε) where union := Graph.union

@[simp]
lemma union_vxSet (G H : Graph α ε) : (G ∪ H).V = G.V ∪ H.V := rfl

@[simp]
lemma union_edgeSet (G H : Graph α ε) : (G ∪ H).E = G.E ∪ H.E := rfl

lemma union_inc₂_iff : (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y) := Iff.rfl

lemma union_le {H₁ H₂ : Graph α ε} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : ε⦄ ⦃x y : α⦄, H₁.Inc₂ e x y ∨ e ∉ H₁.E ∧ H₂.Inc₂ e x y → G.Inc₂ e x y by
    simpa [le_iff, vxSet_subset_of_le h₁, vxSet_subset_of_le h₂, union_inc₂_iff]
  rintro e x y (h | ⟨-, h⟩) <;>
  exact h.of_le <| by assumption

lemma inc₂_or_inc₂_of_union (h : (G ∪ H).Inc₂ e x y) : G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  rw [union_inc₂_iff] at h
  tauto

@[simp]
lemma left_le_union (G H : Graph α ε) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_inc₂_iff]
  tauto

protected lemma union_assoc (G₁ G₂ G₃ : Graph α ε) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_inc₂_iff]
  tauto

lemma Compatible.union_inc₂_iff (h : Compatible G H) :
    (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  by_cases heG : e ∈ G.E
  · simp only [Graph.union_inc₂_iff, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun heH ↦ by rwa [h heG heH.edge_mem]
  simp [Graph.union_inc₂_iff, heG]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..) fun _ _ _ ↦ by rw [h.union_inc₂_iff, h.symm.union_inc₂_iff, or_comm]

lemma Compatible.right_le_union (h : Compatible G H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α ε} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h ↦ ⟨(left_le_union ..).trans h, (h_compat.right_le_union ..).trans h⟩,
    fun h ↦ union_le h.1 h.2⟩

lemma Compatible.of_disjoint_edgeSet (h : Disjoint G.E H.E) : Compatible G H :=
  fun _ heG heH ↦ False.elim <| h.not_mem_of_mem_left heG heH

lemma union_eq_union_edgeDelete (G H : Graph α ε) : G ∪ H = G ∪ (H ＼ G.E) :=
  Graph.ext rfl fun e x y ↦ by rw [union_inc₂_iff,
    (Compatible.of_disjoint_edgeSet disjoint_sdiff_right).union_inc₂_iff, edgeDelete_inc₂, and_comm]

lemma Compatible.mono_left {G₀ : Graph α ε} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H := by
  intro e heG heH
  ext x y
  rw [← inc₂_iff_inc₂_of_le_of_mem hG₀ heG, h (edgeSet_subset_of_le hG₀ heG) heH]

lemma Compatible.mono_right {H₀ : Graph α ε} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α ε} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (union_le hle rfl.le).antisymm (Compatible.right_le_union (H.compatible_self.mono_left hle))

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (union_le rfl.le hle).antisymm <| left_le_union ..

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e heG heH
  ext x y
  obtain ⟨u, v, heuv : G.Inc₂ e u v, hu, hv⟩ := heG
  simp only [induce_inc₂, ← h heuv.edge_mem heH, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq_of_inc₂ heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
    G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) {X : Set α} :
    G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

@[simp]
lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_inc₂, h.union_inc₂_iff, h.induce.union_inc₂_iff]
  tauto

lemma induce_union (G : Graph α ε) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_inc₂, mem_union, Compatible.induce_induce.union_inc₂_iff]
  by_cases hxy : G.Inc₂ e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

lemma Compatible.vxDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  refine Graph.ext union_diff_distrib fun e x y ↦ ?_
  simp only [vxDelete_inc₂, union_vxSet, mem_union]
  rw [vxDelete_def, vxDelete_def, ((h.induce_left _).induce_right _).union_inc₂_iff,
    h.union_inc₂_iff]
  simp only [induce_inc₂, mem_diff]
  by_cases hG : G.Inc₂ e x y
  · simp +contextual [hG, hG.vx_mem_left, hG.vx_mem_right]
  by_cases hH : H.Inc₂ e x y
  · simp +contextual [hH, hH.vx_mem_left, hH.vx_mem_right]
  simp [hG, hH]

lemma edgeRestrict_union (G : Graph α ε) (F₁ F₂ : Set ε) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_inc₂_iff]
  simp only [edgeRestrict_inc₂, mem_union]
  tauto

lemma edgeRestrict_union_edgeDelete (G : Graph α ε) (F : Set ε) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α ε) (F : Set ε) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

lemma induce_union_edgeDelete (G : Graph α ε) (hX : X ⊆ G.V) : G[X] ∪ (G ＼ G[X].E) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

lemma edgeDelete_union_incude (G : Graph α ε) (hX : X ⊆ G.V) : (G ＼ G[X].E) ∪ G[X] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
  simp [disjoint_sdiff_left]

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ G.E → G.Inc₂ e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_inc₂_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).inc₂_iff, Graph.singleEdge_inc₂_iff, and_iff_right rfl, Sym2.eq_iff]
  tauto

lemma exists_compatible_of_le (h : H ≤ G) : ∃ H' : Graph α ε, H.Compatible H' ∧ H ∪ H' = G := by
  use G ＼ H.E, fun e heH he ↦ by simp [heH] at he, le_antisymm ?_ ?_
  · exact le_of_le_le_subset_subset (union_le h edgeDelete_le) le_rfl
      (by simp [vxSet_subset_of_le h]) (by simp [edgeSet_subset_of_le h])
  · rw [le_iff]
    simp only [union_vxSet, edgeDelete_vxSet, subset_union_right, true_and]
    rintro e u v hbtw
    rw [union_inc₂_iff]
    refine (em (e ∈ H.E)).imp ?_ ?_ <;> rintro he
    · simp [← inc₂_iff_inc₂_of_le_of_mem h he, hbtw]
    · simp [he, hbtw]

/-! ### Induced Subgraphs -/

structure IsInducedSubgraph (H G : Graph α ε) : Prop where
  le : H ≤ G
  inc₂_of_mem : ∀ ⦃e x y⦄, G.Inc₂ e x y → x ∈ H.V → y ∈ H.V → H.Inc₂ e x y

infixl:50 " ≤i " => Graph.IsInducedSubgraph
