import Kura.Constructor
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

structure IsSubgraph (H G : Graph α β) : Prop where
  vx_subset : V(H) ⊆ V(G)
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

def inf (G H : Graph α β) : Graph α β := Graph.mk' (V(G) ∩ V(H))
  (fun e x y ↦ G.IsLink e x y ∧ H.IsLink e x y)
  (fun _ _ _ ⟨hxy1, hxy2⟩ ↦ ⟨hxy1.symm, hxy2.symm⟩)
  (fun _ _ _ _ _ ⟨hxy1, _⟩ ⟨huv1, _⟩ ↦ hxy1.left_eq_or_eq_of_isLink huv1)
  (fun _ _ _ ⟨hxy1, hxy2⟩ ↦ ⟨hxy1.vx_mem_left, hxy2.vx_mem_left⟩)

/-- The subgraph order -/
instance : SemilatticeInf (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.le, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩
  inf := inf
  inf_le_left G H := ⟨inter_subset_left, fun e x y h ↦ h.1⟩
  inf_le_right G H := ⟨inter_subset_right, fun e x y h ↦ h.2⟩
  le_inf _ _ _ h₁ h₂ := ⟨subset_inter h₁.1 h₂.1, fun e x y ↦ imp_and.mpr ⟨(h₁.2 ·), (h₂.2 ·)⟩⟩

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.2 h

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vertexSet_subset_of_le (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

lemma edgeSet_subset_of_le (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq_of_isLink h
  · assumption
  exact huv.symm

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

lemma isLink_eq_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e = H.IsLink e := funext₂ fun x y ↦ by
  rw [isLink_iff_isLink_of_le_of_mem hle he]

lemma parallel.of_le (h : H.parallel e f) (hle : H ≤ G) : G.parallel e f := by
  obtain ⟨he, hf, h⟩ := h
  refine ⟨edgeSet_subset_of_le hle he, edgeSet_subset_of_le hle hf, ?_⟩
  rwa [isLink_eq_isLink_of_le_of_mem hle he, isLink_eq_isLink_of_le_of_mem hle hf]

lemma parallel_iff_parallel_of_le_of_mem (hle : G ≤ H) (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.parallel e f ↔ H.parallel e f := by
  refine ⟨(·.of_le hle), fun ⟨_he, _hf, h⟩ ↦ ?_⟩
  rw [isLink_eq_isLink_of_le_of_mem hle he, isLink_eq_isLink_of_le_of_mem hle hf] at h
  exact ⟨he, hf, h⟩

lemma inc_iff_inc_of_le_of_mem (hle : G ≤ H) (he : e ∈ E(G)) : G.Inc e x ↔ H.Inc e x := by
  revert x
  simp [inc_iff_inc_iff, isLink_iff_isLink_of_le_of_mem hle he]

lemma le_iff_inc : G ≤ H ↔ V(G) ⊆ V(H) ∧ E(G) ⊆ E(H) ∧ ∀ e ∈ E(G), ∀ v,
  G.Inc e v ↔ H.Inc e v := by
  constructor
  · rintro hle
    refine ⟨vertexSet_subset_of_le hle, edgeSet_subset_of_le hle, fun e he v ↦ ?_⟩
    rw [inc_iff_inc_of_le_of_mem hle he]
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, fun e x y ↦ ?_⟩
    by_cases he : e ∈ E(G)
    · rw [inc_eq_inc_iff.mp (by ext; exact hinc e he _)]
      exact id
    · simp [he]

lemma toMultiset_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.toMultiset e = G.toMultiset e := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  rw [toMultiset_eq_pair_iff.mpr h, toMultiset_eq_pair_iff.mpr (h.of_le hle)]

lemma toSym2_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) :
    H.toSym2 e he = G.toSym2 e (edgeSet_subset_of_le hle he) := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  rw [(toSym2_eq_pair_iff he).mpr h,
    (toSym2_eq_pair_iff (edgeSet_subset_of_le hle he)).mpr (h.of_le hle)]

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  vx_subset := hV
  isLink_of_isLink e x y h := by
    rw [← G.isLink_iff_isLink_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

instance instvxNonemptyOfEdgeNonempty (G : Graph α β) [hE : Nonempty E(G)] : Nonempty V(G) := by
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet hE.some.prop
  use x, hbtw.vx_mem_left

instance instWellFoundedLTGraph [Finite α] [Finite β] : WellFoundedLT (Graph α β) := by
  let f : Graph α β → ℕ := fun G ↦ V(G).ncard + E(G).ncard
  have hf : StrictMono f := by
    rintro G H hlt
    simp only [f]
    obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hlt
    obtain hV | hV := ssubset_or_eq_of_subset <| vertexSet_subset_of_le hle
    · have hE' : E(G) ⊆ E(H) := edgeSet_subset_of_le hle
      have hE'ncard : E(G).ncard ≤ E(H).ncard := ncard_le_ncard hE'
      have hVncard : V(G).ncard < V(H).ncard := ncard_lt_ncard hV (toFinite V(H))
      exact Nat.add_lt_add_of_lt_of_le hVncard hE'ncard
    rw [hV]
    obtain hE | hE := ssubset_or_eq_of_subset <| edgeSet_subset_of_le hle
    · have hEncard : E(G).ncard < E(H).ncard := ncard_lt_ncard hE (toFinite E(H))
      exact Nat.add_lt_add_left hEncard V(H).ncard
    obtain rfl := ext_of_le_le hle le_rfl hV hE
    simp only [ne_eq, not_true_eq_false, f] at hne
  exact hf.wellFoundedLT

lemma minimal_exist {P : Graph α β → Prop} [Finite α] [Finite β] (h : P G) :
    ∃ G : Graph α β, Minimal P G :=
  exists_minimal_of_wellFoundedLT _ (by use G)

lemma forall_of_minimal_not_exist {P : Graph α β → Prop} [Finite α] [Finite β]
    (h : ¬ ∃ G : Graph α β, Minimal (¬ P ·) G) : P G := by
  contrapose! h
  exact minimal_exist h

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e x y h := by rwa [G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_isLink h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [h, G.exists_isLink_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_isLink _ _ _ h := h.2.vx_mem_left

scoped infixl:65 " ↾ "  => Graph.edgeRestrict

lemma IsLink.edgeRestrict (hG : G.IsLink e x y) (he : e ∈ F) : (G ↾ F).IsLink e x y := by
  rw [edgeRestrict_isLink]
  exact ⟨he, hG⟩

lemma IsLink.of_edgeRestrict (hG : (G ↾ F).IsLink e x y) : G.IsLink e x y := by
  rw [edgeRestrict_isLink] at hG
  exact hG.2

@[simp]
lemma edgeRestrict_inc : (G ↾ F).Inc e x ↔ e ∈ F ∧ G.Inc e x := by
  simp_rw [inc_iff_exists_isLink, edgeRestrict_isLink, exists_and_left]

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vx_subset := rfl.le
  isLink_of_isLink := by simp

lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vx_subset := rfl.subset
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F :=
  G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vertexSet_subset_of_le h)
    (by simp [inter_subset_right.trans (edgeSet_subset_of_le h)])

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_eq_self_iff (G : Graph α β) (F : Set β) : G ↾ F = G ↔ E(G) ⊆ F := by
  constructor <;> intro h
  · rw [← h]
    simp [edgeRestrict_edgeSet, inter_subset_left]
  · refine le_antisymm edgeRestrict_le ?_
    rw [ext_of_le_le edgeRestrict_le le_rfl rfl]
    exact inter_eq_right.mpr h

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le (edgeRestrict_le.trans (by simp)) (by simp) (by simp) ?_
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma edgeRestrict_le_edgeRestrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ ≤ G ↾ F₂ ↔ F₁ ∩ E(G) ⊆ F₂ ∩ E(G) := by
  refine ⟨fun h e he ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_inter_iff] at he ⊢
    simp [he, (edgeSet_subset_of_le h he).1]
  · refine ⟨subset_rfl, fun e x y hbtw ↦ ?_⟩
    rw [edgeRestrict_isLink] at hbtw ⊢
    exact ⟨(h ⟨hbtw.1, hbtw.2.edge_mem⟩).1, hbtw.2⟩

@[simp]
lemma edgeRestrict_eq_edgeRestrict_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ↾ F₁ = G ↾ F₂ ↔ F₁ ∩ E(G) = F₂ ∩ E(G) := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeRestrict_le_edgeRestrict_iff, edgeRestrict_le_edgeRestrict_iff]

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`, but we also
use `copy` for better definitional properties. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F) (IsLink := fun e x y ↦ e ∉ F ∧ G.IsLink e x y) rfl
    (by simp [diff_subset])
    (fun e x y ↦ by
      simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
      exact fun h _ ↦ h.edge_mem)

scoped infixl:65 " ＼ " => Graph.edgeDelete

@[simp]
lemma edgeDelete_edgeSet_subset (G : Graph α β) (F : Set β) : E(G ＼ F) ⊆ E(G) := by
  simp [edgeDelete_edgeSet]
  exact diff_subset

@[simp]
lemma edgeDelete_edgeSet_ncard_le (G : Graph α β) (F : Set β) [Finite E(G)] :
    E(G ＼ F).ncard ≤ E(G).ncard := ncard_le_ncard <| G.edgeDelete_edgeSet_subset F

@[simp↓]
lemma edgeDelete_edgeSet_ncard_lt_iff (G : Graph α β) (F : Set β) [Finite E(G)] :
    E(G ＼ F).ncard < E(G).ncard ↔ (E(G) ∩ F).Nonempty := by
  rw [edgeDelete_edgeSet]
  refine ⟨fun h ↦ ?_, fun h ↦ ncard_lt_ncard <| diff_ssubset_left_iff.mpr h⟩
  by_contra! h'
  rw [← disjoint_iff_inter_eq_empty] at h'
  simp only [h'.sdiff_eq_left, lt_self_iff_false] at h

@[simp↓]
lemma edgeDelete_singleton_edgeSet_ncard_lt_iff (G : Graph α β) (e : β) [Finite E(G)] :
    E(G ＼ {e}).ncard < E(G).ncard ↔ e ∈ E(G) := by
  simp only [edgeDelete_edgeSet_ncard_lt_iff, inter_singleton_nonempty]

lemma IsLink.edgeDelete (hG : G.IsLink e x y) (he : e ∉ F) : (G ＼ F).IsLink e x y := by
  rw [edgeDelete_isLink]
  exact ⟨he, hG⟩

lemma IsLink.of_edgeDelete (hG : (G ＼ F).IsLink e x y) : G.IsLink e x y := by
  rw [edgeDelete_isLink] at hG
  exact hG.2

@[simp]
lemma edgeDelete_inc : (G ＼ F).Inc e x ↔ e ∉ F ∧ G.Inc e x := by
  simp_rw [inc_iff_exists_isLink, edgeDelete_isLink, exists_and_left]

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_subset_of_le h)

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ↾ F₁ ＼ F₂ = G ↾ (F₁ \ F₂) := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

@[simp]
lemma edgeDelete_eq_self_iff (G : Graph α β) (F : Set β) : G ＼ F = G ↔ Disjoint E(G) F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_eq_self_iff, ← Set.subset_compl_iff_disjoint_right,
    diff_eq_compl_inter]
  simp only [subset_inter_iff, subset_refl, and_true]

lemma edgeDelete_eq_self (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

@[simp]
lemma edgeDelete_le_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ ≤ G ＼ F₂ ↔ E(G) \ F₁ ⊆ E(G) \ F₂ := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, edgeRestrict_le_edgeRestrict_iff,
    inter_eq_left.mpr diff_subset, inter_eq_left.mpr diff_subset]

@[simp]
lemma edgeDelete_eq_edgeDelete_iff (G : Graph α β) (F₁ F₂ : Set β) :
    G ＼ F₁ = G ＼ F₂ ↔ E(G) \ F₁ = E(G) \ F₂ := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeDelete_le_edgeDelete, edgeDelete_le_edgeDelete]

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
    not_isLink_of_notMem_edgeSet, iff_false, not_and]
  exact fun h hbtw ↦ h (hF hbtw.edge_mem)

instance instOrderBotGraph : OrderBot (Graph α β) where
  bot := Graph.noEdge ∅ β
  bot_le G := by
    rw [le_iff_inc]
    refine ⟨?_, ?_⟩ <;> simp [Graph.noEdge, empty_subset, mem_empty_iff_false,
    false_iff, IsEmpty.forall_iff, implies_true]

@[simp] lemma noEdge_empty_eq_bot : Graph.noEdge (∅ : Set α) β = ⊥ := rfl

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥

@[simp] lemma bot_V : V((⊥ : Graph α β)) = ∅ := rfl

@[simp] lemma bot_E : E((⊥ : Graph α β)) = ∅ := rfl

instance instVxSetIsEmptyBot : IsEmpty V((⊥ : Graph α β)) := by
  simp

instance instESetIsEmptyBot : IsEmpty E((⊥ : Graph α β)) := by
  simp

@[simp]
lemma vertexSet_empty_iff_eq_bot : V(G) = ∅ ↔ G = ⊥ := by
  constructor <;> rintro h
  · apply ext_inc h ?_
    simp only [bot_E, mem_empty_iff_false, not_false_eq_true, not_inc_of_notMem_edgeSet, iff_false]
    rintro e v hinc
    have := h ▸ hinc.vx_mem
    simp only [mem_empty_iff_false] at this
  · rw [h]
    rfl

instance instUniqueGraph [IsEmpty α] : Unique (Graph α β) where
  default := ⊥
  uniq G := by
    rw [← vertexSet_empty_iff_eq_bot]
    exact eq_empty_of_isEmpty V(G)

@[simp] lemma eq_bot_of_isEmpty [IsEmpty α] : G = ⊥ := instUniqueGraph.uniq G

@[simp]
lemma bot_not_isLink : ¬ (⊥ : Graph α β).IsLink e x y := by
  intro h
  simpa using h.vx_mem_left

@[simp]
lemma bot_not_inc : ¬ (⊥ : Graph α β).Inc e x := by
  intro h
  simpa using h.choose_spec.vx_mem_left

@[simp]
lemma bot_not_adj : ¬ (⊥ : Graph α β).Adj x y := by
  intro h
  simpa using h.choose_spec.vx_mem_left


@[simp]
lemma edgeDelete_empty : G ＼ (∅ : Set β) = G := by
  simp

@[simp]
lemma edgeDelete_edgeSet_eq_bot : (G ＼ E(G)) = Graph.noEdge V(G) β := by
  simp only [subset_refl, edgeDelete_eq_noEdge]

@[simp]
lemma edgeDelete_univ : G ＼ (univ : Set β) = Graph.noEdge V(G) β := by
  simp [edgeDelete_eq_noEdge]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β := Graph.mk'
  (V := X)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ x ∈ X ∧ y ∈ X)
  (isLink_symm := fun e x y ↦ by simp [G.isLink_comm, and_comm (a := (x ∈ X))])
  (eq_or_eq_of_isLink_of_isLink := fun e x y u v ⟨h, _⟩ ⟨h', _⟩ ↦ G.eq_or_eq_of_isLink_of_isLink h h')
  (vx_mem_left_of_isLink := fun _ _ _ ⟨_, h⟩ ↦ h.1)

notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

lemma IsLink.induce (hG : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y := by
  rw [induce_isLink]
  exact ⟨hG, hx, hy⟩

lemma IsLink.of_induce (hG : G[X].IsLink e x y) : G.IsLink e x y := by
  rw [induce_isLink] at hG
  exact hG.1

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G[X]) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) :
    E(G[X]) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma IsLink.mem_induce_iff {X : Set α} (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq_of_isLink he <;> simp [hx', hy']

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink, edgeRestrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

lemma induce_mono (hle : H ≤ G) (hsu : X ⊆ Y) : H[X] ≤ G[Y] := by
  rw [le_iff]
  refine ⟨hsu, fun e x y ↦ ?_⟩
  rw [induce_isLink, induce_isLink]
  exact fun ⟨hbtw, hxU, hyU⟩ ↦ ⟨hbtw.of_le hle, hsu hxU, hsu hyU⟩

lemma induce_mono_left (hle : H ≤ G) (X : Set α) : H[X] ≤ G[X] :=
  induce_mono hle subset_rfl

lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] :=
  induce_mono (le_refl G) hXY

@[simp]
lemma induce_le_induce_iff (G : Graph α β) (X Y : Set α) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨vertexSet_subset_of_le, induce_mono_right G⟩

@[simp]
lemma induce_eq_induce_iff (G : Graph α β) (X Y : Set α) : G[X] = G[Y] ↔ X = Y := by
  rw [le_antisymm_iff, induce_le_induce_iff, induce_le_induce_iff, antisymm_iff]

@[simp]
lemma induce_eq_self_iff (G : Graph α β) (X : Set α) : G[X] = G ↔ X = V(G) := by
  constructor <;> intro h
  · rw [← h]
    rfl
  · simp only [le_antisymm_iff, induce_le h.le, true_and]
    subst X
    rw [le_iff]
    refine ⟨subset_refl _, fun e x y hbtw ↦ ?_⟩
    rw [induce_isLink]
    exact ⟨hbtw, hbtw.vx_mem_left, hbtw.vx_mem_right⟩

@[simp]
lemma induce_empty : G[∅] = ⊥ := by
  rw [← vertexSet_empty_iff_eq_bot]
  rfl

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vxDelete (G : Graph α β) (X : Set α) : Graph α β := G [V(G) \ X]

instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
  hSub := Graph.vxDelete

lemma vxDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vxDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp]
lemma vxDelete_edgeSet (G : Graph α β) (X : Set α) :
  E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ (x ∈ V(G) ∧ x ∉ X) ∧ y ∈ V(G) ∧ y ∉ X}  := rfl

@[simp]
lemma vxDelete_isLink (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ (x ∈ V(G) ∧ x ∉ X) ∧ y ∈ V(G) ∧ y ∉ X) := Iff.rfl

@[simp]
lemma vxDelete_le : G - X ≤ G :=
  G.induce_le diff_subset

lemma IsLink.mem_vxDelete_iff {X : Set α} (hG : G.IsLink e x y) : e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vxDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.vx_mem_left,
    and_iff_right hG.vx_mem_right]

@[simp]
theorem vxDelete_eq_self_iff : G - X = G ↔ Disjoint X V(G) := by
  simp only [vxDelete_def, induce_eq_self_iff, sdiff_eq_left, disjoint_comm]

lemma vxDelete_mono_left (hle : G ≤ H) : G - X ≤ H - X := by
  simp [vxDelete_def]
  exact induce_mono hle (diff_subset_diff_left <| vertexSet_subset_of_le hle)

lemma vxDelete_anti_right (hsu : Y ⊆ X) : G - X ≤ G - Y := by
  simp only [vxDelete_def, induce_le_induce_iff]
  exact diff_subset_diff_right hsu

@[simp]
lemma vxDelete_le_vxDelete_iff : G - X ≤ G - Y ↔ V(G) \ X ⊆ V(G) \ Y := by
  simp_rw [vxDelete_def, induce_le_induce_iff]

@[simp]
lemma vxDelete_eq_vxDelete_iff : G - X = G - Y ↔ V(G) \ X = V(G) \ Y := by
  simp_rw [vxDelete_def, induce_eq_induce_iff]

@[simp]
lemma vxDelete_empty : G - (∅ : Set α) = G := by
  simp [vxDelete_def]

@[simp]
lemma vxDelete_V : G - (V(G) : Set α) = ⊥ := by
  simp [vxDelete_def]

@[simp]
lemma vxDelete_univ : G - (univ : Set α) = ⊥ := by
  simp [vxDelete_def]

-- TODO: prove some lemmas about `G - X`

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink, edgeRestrict_isLink]
  tauto

lemma edgeRestrict_vxDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vxDelete_isLink, edgeRestrict_isLink, edgeRestrict_vertexSet]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vxDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by simp +contextual

@[simp]
lemma vxDelete_induce (G : Graph α β) (X D : Set α) : (G - D)[X] = G[X] ↾ E(G - D) :=
  induce_induce G (V(G) \ D) X

@[simp]
lemma vxDelete_vxDelete : G - X - Y = G - (X ∪ Y) := by
  rw [G.vxDelete_def, induce_vxDelete, diff_diff]
  rfl

@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v := by
  simp only [le_iff, singleEdge_vertexSet, Set.pair_subset_iff, singleEdge_isLink_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.vx_mem_left, h.vx_mem_right⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → G.IsLink e = H.IsLink e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [← isLink_iff_isLink_of_le_of_mem h₁ he₁, ← isLink_iff_isLink_of_le_of_mem h₂ he₂]

lemma compatible_self (G : Graph α β) : G.Compatible G := by
  simp [Compatible]

lemma compatible_iff_inter_edge_eq_inter : G.Compatible H ↔ E(G ⊓ H) = E(G) ∩ E(H) := by
  constructor
  · rintro h
    ext e
    simp only [mem_setOf_eq, mem_inter_iff]
    refine ⟨fun ⟨x, y, hG, hH⟩ ↦ ⟨hG.edge_mem, hH.edge_mem⟩, fun ⟨heG, heH⟩ ↦ ?_⟩
    · obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet heG
      exact ⟨x, y, hbtw, (h heG heH) ▸ hbtw⟩
  · rintro h e heG heH
    have : e ∈ E(G) ∩ E(H) := ⟨heG, heH⟩
    obtain ⟨u, v, hbtwG, hbtwH⟩ := h ▸ this
    rw [← toSym2_eq_pair_iff (by assumption)] at hbtwG hbtwH
    rw [← toSym2_eq_toSym2_iff heG heH, hbtwG, hbtwH]

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e x y h := by rwa [G.isLink_comm, H.isLink_comm]
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_eq_or_eq_of_isLink h'
    · exact False.elim <| h'.1 h.edge_mem
    · exact False.elim <| h.1 h'.edge_mem
    exact h.2.left_eq_or_eq_of_isLink h'.2
  edge_mem_iff_exists_isLink e := by
    refine ⟨?_, fun ⟨x, y, h⟩ ↦ h.elim (fun h' ↦ .inl h'.edge_mem) (fun h' ↦ .inr h'.2.edge_mem)⟩
    rw [← Set.union_diff_self]
    rintro (he | ⟨heH, heG⟩)
    · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, .inl h⟩
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heH
    exact ⟨x, y, .inr ⟨heG, h⟩⟩
  vx_mem_left_of_isLink := by
    rintro e x y (h | h)
    · exact .inl h.vx_mem_left
    exact .inr h.2.vx_mem_left

instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vertexSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

lemma union_isLink_iff : (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : β⦄ ⦃x y : α⦄, H₁.IsLink e x y ∨ e ∉ E(H₁) ∧ H₂.IsLink e x y → G.IsLink e x y by
    simpa [le_iff, vertexSet_subset_of_le h₁, vertexSet_subset_of_le h₂, union_isLink_iff]
  rintro e x y (h | ⟨-, h⟩) <;>
  exact h.of_le <| by assumption

lemma isLink_or_isLink_of_union (h : (G ∪ H).IsLink e x y) : G.IsLink e x y ∨ H.IsLink e x y := by
  rw [union_isLink_iff] at h
  tauto

@[simp]
lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink_iff]
  tauto

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

lemma Compatible.union_isLink_iff (h : Compatible G H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink_iff, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun heH ↦ by rwa [h heG heH.edge_mem]
  simp [Graph.union_isLink_iff, heG]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..) fun _ _ _ ↦ by rw [h.union_isLink_iff, h.symm.union_isLink_iff, or_comm]

lemma Compatible.right_le_union (h : Compatible G H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h ↦ ⟨(left_le_union ..).trans h, (h_compat.right_le_union ..).trans h⟩,
    fun h ↦ union_le h.1 h.2⟩

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH ↦ False.elim <| h.notMem_of_mem_left heG heH

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) :=
  Graph.ext rfl fun e x y ↦ by rw [union_isLink_iff,
    (Compatible.of_disjoint_edgeSet disjoint_sdiff_right).union_isLink_iff, edgeDelete_isLink, and_comm]

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H := by
  intro e heG heH
  ext x y
  rw [← isLink_iff_isLink_of_le_of_mem hG₀ heG, h (edgeSet_subset_of_le hG₀ heG) heH]

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (union_le hle rfl.le).antisymm (Compatible.right_le_union (H.compatible_self.mono_left hle))

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (union_le rfl.le hle).antisymm <| left_le_union ..

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e heG heH
  ext x y
  obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
  simp only [induce_isLink, ← h heuv.edge_mem heH, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq_of_isLink heuv <;> simp_all

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
  simp only [induce_isLink, h.union_isLink_iff, h.induce.union_isLink_iff]
  tauto

lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink, mem_union, Compatible.induce_induce.union_isLink_iff]
  by_cases hxy : G.IsLink e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

lemma Compatible.vxDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  refine Graph.ext union_diff_distrib fun e x y ↦ ?_
  simp only [vxDelete_isLink, union_vertexSet, mem_union]
  rw [vxDelete_def, vxDelete_def, ((h.induce_left _).induce_right _).union_isLink_iff,
    h.union_isLink_iff]
  simp only [induce_isLink, mem_diff]
  by_cases hG : G.IsLink e x y
  · simp +contextual [hG, hG.vx_mem_left, hG.vx_mem_right]
  by_cases hH : H.IsLink e x y
  · simp +contextual [hH, hH.vx_mem_left, hH.vx_mem_right]
  simp [hG, hH]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink_iff]
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

lemma induce_union_edgeDelete (G : Graph α β) (hX : X ⊆ V(G)) : G[X] ∪ (G ＼ E(G[X])) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

lemma edgeDelete_union_induce (G : Graph α β) (hX : X ⊆ V(G)) : (G ＼ E(G[X])) ∪ G[X] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
  simp [disjoint_sdiff_left]

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ E(G) → G.IsLink e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_isLink_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).isLink_iff, Graph.singleEdge_isLink_iff, and_iff_right rfl, Sym2.eq_iff]
  tauto

lemma exists_compatible_of_le (h : H ≤ G) : ∃ H' : Graph α β, H.Compatible H' ∧ H ∪ H' = G := by
  use G ＼ E(H), fun e heH he ↦ by simp [heH] at he, le_antisymm ?_ ?_
  · exact le_of_le_le_subset_subset (union_le h edgeDelete_le) le_rfl
      (by simp [vertexSet_subset_of_le h]) (by simp [edgeSet_subset_of_le h])
  · rw [le_iff]
    simp only [union_vertexSet, edgeDelete_vertexSet, subset_union_right, true_and]
    rintro e u v hbtw
    rw [union_isLink_iff]
    refine (em (e ∈ E(H))).imp ?_ ?_ <;> rintro he
    · simp [← isLink_iff_isLink_of_le_of_mem h he, hbtw]
    · simp [he, hbtw]

/-! ### Induced Subgraphs -/

structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

infixl:50 " ≤i " => Graph.IsInducedSubgraph
