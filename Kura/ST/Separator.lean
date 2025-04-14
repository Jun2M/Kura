import Kura.Operation.Subgraph
import Kura.Walk.Operation


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G G' H H' : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}


@[mk_iff]
structure IsVxSeparator (G : Graph α β) (u v : α) (S : Set α) : Prop where
  not_mem_left : u ∉ S
  not_mem_right : v ∉ S
  not_connected : ¬ (G [G.V \ S]).Connected u v

lemma not_exists_isSeparator_self (hu : u ∈ G.V) : ¬ ∃ S, G.IsVxSeparator u u S :=
  fun ⟨S, hS⟩ ↦ hS.not_connected <| Connected.refl <| by simp [hu, hS.not_mem_left]

-- lemma IsVxSeparator.iff_edgeDel_singleton_isLoop {S : Set α} (he : G.IsLoop e) :
--     G.IsVxSeparator u v S ↔ (G -ᴳ e).IsVxSeparator u v S := by
--   refine ⟨fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩, fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩⟩
--   · by_cases he' : e ∈ G[G.V \ S].E
--     · rw [restrict_V, ← induce_restrict_eq_subgraph]
--       rw [← IsLoop.connected_iff_edgeDel_singleton (e := e)] at hconn
--       convert hconn using 2
--       rw [restrict_eq_restrict_iff]
--       ext e
--       simp +contextual only [induce_E, mem_diff, mem_inter_iff, mem_setOf_eq, mem_singleton_iff,
--         and_self_left, and_congr_right_iff, true_and, implies_true]
--       rwa [IsLoopAt_iff_IsLoopAt_of_edge_mem_le (induce_le G diff_subset) he']
--     · rwa [restrict_V, subgraph_eq_induce]
--       rintro e'
--       simp +contextual only [mem_diff, mem_setOf_eq, mem_singleton_iff]
--       rintro hx
--       sorry
--   · sorry

def IsVxSetSeparator (G : Graph α β) (S T V : Set α) : Prop := ¬ (G - V).SetConnected S T

namespace IsVxSetSeparator
variable {U V S S' T T' : Set α} (h : G.IsVxSetSeparator S T V)

def leftSet (h : G.IsVxSetSeparator S T V) : Set α :=
  {v | ∃ s ∈ S, (G - V).Connected v s}

def rightSet (h : G.IsVxSetSeparator S T V) : Set α :=
  {v | ∃ t ∈ T, (G - V).Connected v t}

@[simp] lemma not_isVxSetSeparator : ¬ G.IsVxSetSeparator S T V ↔ (G - V).SetConnected S T := by
  simp [IsVxSetSeparator]

@[simp]
lemma le (h : G'.IsVxSetSeparator S T V) (hle : G ≤ G') : G.IsVxSetSeparator S T V :=
  fun hconn ↦ h <| hconn.le <| vxDel_le_vxDel_of_subset hle fun ⦃_⦄ a ↦ a

lemma symm (h : G.IsVxSetSeparator S T V) : G.IsVxSetSeparator T S V := (h ·.symm)

lemma comm : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator T S V := ⟨symm, symm⟩

@[simp]
lemma sep_subset (h : G.IsVxSetSeparator S T U) (hUV : U ⊆ V) : G.IsVxSetSeparator S T V :=
  fun hconn ↦ h <| hconn.le <| vxDel_anti G hUV

@[simp]
lemma subset_source (h : G.IsVxSetSeparator S' T V) (hS : S ⊆ S') : G.IsVxSetSeparator S T V :=
  fun hconn ↦ h <| hconn.left_subset hS

@[simp]
lemma subset_target (h : G.IsVxSetSeparator S T' V) (hT : T ⊆ T') : G.IsVxSetSeparator S T V :=
  fun hconn ↦ h <| hconn.right_subset hT

@[simp]
lemma empty_iff : G.IsVxSetSeparator S T ∅ ↔ ¬ G.SetConnected S T := by simp [IsVxSetSeparator]

@[simp] lemma empty_source : G.IsVxSetSeparator ∅ T V := by simp [IsVxSetSeparator]

@[simp] lemma empty_target : G.IsVxSetSeparator S ∅ V := by simp [IsVxSetSeparator]

@[simp] lemma univ_sep : G.IsVxSetSeparator S T univ := by simp [IsVxSetSeparator]

@[simp] lemma support_sep : G.IsVxSetSeparator S T G.V := by simp [IsVxSetSeparator]

lemma sep_support : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator S T (V ∩ G.V) := by
  unfold IsVxSetSeparator
  suffices G - V = G - (V ∩ G.V) by rw [this]
  rw [vxDel_eq_vxDel_iff]
  simp

lemma left_support : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator (S ∩ G.V) T V := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.left_supported, vxDel_V] at hconn ⊢
    exact hconn.left_subset (by tauto_set)
  · rw [SetConnected.left_supported, vxDel_V] at hconn
    exact hconn.left_subset (by tauto_set)

lemma right_support : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator S (T ∩ G.V) V := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.right_supported, vxDel_V] at hconn ⊢
    exact hconn.right_subset (by tauto_set)
  · rw [SetConnected.right_supported, vxDel_V] at hconn
    exact hconn.right_subset (by tauto_set)

lemma left_right_support : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator (S ∩ G.V) (T ∩ G.V) V := by
  rw [left_support, right_support]

lemma left_diff_sep : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator (S \ V) T V := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.left_supported, vxDel_V] at hconn ⊢
    exact hconn.left_subset (by tauto_set)
  · rw [SetConnected.left_supported, vxDel_V] at hconn
    exact hconn.left_subset (by tauto_set)

lemma right_diff_sep : G.IsVxSetSeparator S T V ↔ G.IsVxSetSeparator S (T \ V) V := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.right_supported, vxDel_V] at hconn ⊢
    exact hconn.right_subset (by tauto_set)
  · rw [SetConnected.right_supported, vxDel_V] at hconn
    exact hconn.right_subset (by tauto_set)

lemma source_inter_target_subset (h : G.IsVxSetSeparator S T V) : G.V ∩ S ∩ T ⊆ V := by
  rintro x ⟨⟨hx, hxS⟩, hxT⟩
  by_contra! hxV
  apply h
  use x, hxS, x, hxT, Connected.refl ⟨hx, hxV⟩

@[simp]
lemma vxDel : (G - U).IsVxSetSeparator S T V ↔ G.IsVxSetSeparator S T (U ∪ V) := by
  unfold IsVxSetSeparator
  rw [vxDel_vxDel_eq_vxDel_union]

/- Lemmas about the left and right sets of a separator -/
lemma leftSet_subset (h : G.IsVxSetSeparator S T V) : h.leftSet ⊆ G.V \ V :=
  fun _v ⟨_s, _hs, hconn⟩ ↦ hconn.mem_left

lemma subset_leftSet (h : G.IsVxSetSeparator S T V) (hS : S ⊆ G.V) : S ⊆ h.leftSet ∪ V := by
  rintro s hs
  by_cases h' : s ∈ V
  · exact Or.inr h'
  · left
    use s, hs, Connected.refl ⟨hS hs, h'⟩

lemma rightSet_subset (h : G.IsVxSetSeparator S T V) : h.rightSet ⊆ G.V \ V :=
  fun _v ⟨_t, _ht, hconn⟩ ↦ hconn.mem_left

lemma subset_rightSet (h : G.IsVxSetSeparator S T V) (hT : T ⊆ G.V) : T ⊆ h.rightSet ∪ V := by
  rintro t ht
  by_cases h' : t ∈ V
  · exact Or.inr h'
  · left
    use t, ht, Connected.refl ⟨hT ht, h'⟩

@[simp]
lemma symm_leftSet (h : G.IsVxSetSeparator S T V) : h.symm.leftSet = h.rightSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma symm_rightSet (h : G.IsVxSetSeparator S T V) : h.symm.rightSet = h.leftSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma leftSet_rightSet_disjoint (h : G.IsVxSetSeparator S T V) :
    Disjoint h.leftSet h.rightSet := by
  rintro U hUl hUr a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  obtain ⟨t, ht, hconn'⟩ := hUr haU
  apply h
  use s, hs, t, ht, hconn.symm.trans hconn'

@[simp]
lemma leftSet_V_disjoint (h : G.IsVxSetSeparator S T V) : Disjoint h.leftSet V := by
  rintro U hUl hUV a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma rightSet_V_disjoint (h : G.IsVxSetSeparator S T V) : Disjoint h.rightSet V := by
  rintro U hUr hUV a haU
  obtain ⟨t, ht, hconn⟩ := hUr haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma leftSetV_inter_rightSetV (h : G.IsVxSetSeparator S T V) :
    (h.leftSet ∪ V) ∩ (h.rightSet ∪ V) = V := by
  ext a
  simp +contextual only [mem_inter_iff, mem_union, iff_def, and_imp, or_true, and_self,
    implies_true, and_true]
  rintro (hl | hl) (hr | hr) <;> try assumption
  have := h.leftSet_rightSet_disjoint (by simp [hl] : {a} ≤ _) (by simp [hr] : {a} ≤ _)
  simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at this

lemma leftSet_Sep_compl (h : G.IsVxSetSeparator S T V) :
    G.IsVxSetSeparator h.leftSet (h.leftSet ∪ V)ᶜ V := by
  refine fun ⟨l, hl, r, hr, hconn⟩ ↦ hr ?_
  left
  obtain ⟨s, hs, hls⟩ := hl
  use s, hs, hconn.symm.trans hls

lemma rightSet_Sep_compl (h : G.IsVxSetSeparator S T V) :
    G.IsVxSetSeparator h.rightSet (h.rightSet ∪ V)ᶜ V := by
  refine fun ⟨l, hl, r, hr, hconn⟩ ↦ hr ?_
  left
  obtain ⟨t, ht, hrt⟩ := hl
  use t, ht, hconn.symm.trans hrt

lemma compl_Sep_leftSet (h : G.IsVxSetSeparator S T V) :
    G.IsVxSetSeparator (h.leftSet ∪ V)ᶜ h.leftSet V := h.leftSet_Sep_compl.symm

lemma compl_Sep_rightSet (h : G.IsVxSetSeparator S T V) :
    G.IsVxSetSeparator (h.rightSet ∪ V)ᶜ h.rightSet V := h.rightSet_Sep_compl.symm

lemma leftSet_Sep_rightSet (h : G.IsVxSetSeparator S T V) :
    G.IsVxSetSeparator h.leftSet h.rightSet V := by
  refine h.leftSet_Sep_compl.subset_target ?_
  simp only [compl_union, subset_inter_iff]
  rw [subset_compl_iff_disjoint_left, subset_compl_iff_disjoint_left]
  exact ⟨h.leftSet_rightSet_disjoint, h.rightSet_V_disjoint.symm⟩

lemma mem_of_inc₂_leftSet (hbtw : G.Inc₂ e u v) (hu : u ∈ h.leftSet) :
    v ∈ h.leftSet ∪ V := by
  obtain ⟨s, hs, hconn⟩ := hu
  by_contra! hvV
  simp only [leftSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at hvV
  obtain ⟨hnconn, hvV⟩ := hvV
  exact hnconn s hs
  <| (hbtw.induce_of_mem hconn.mem_left ⟨hbtw.vx_mem_right, hvV⟩).connected.symm.trans hconn

lemma mem_of_inc₂_rightSet (hbtw : G.Inc₂ e u v) (hv : v ∈ h.rightSet) :
    u ∈ h.rightSet ∪ V := by
  obtain ⟨t, ht, hconn⟩ := hv
  by_contra! huV
  simp only [rightSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at huV
  obtain ⟨hnconn, huV⟩ := huV
  refine hnconn t ht <| hbtw.induce_of_mem (⟨hbtw.vx_mem_left, huV⟩ : u ∈ G.V \ V) hconn.mem_left
  |>.connected.trans hconn

/-- Given a set of edges, there is a separator that puts those edges on one side and the rest of
the edges on the other side. -/
def of_edges (G : Graph α β) (U : Set β) :
    G.IsVxSetSeparator {v | ∃ e ∈ U, G.Inc e v} {v | ∃ e ∉ U, G.Inc e v} {v | (∃ e ∈ U, G.Inc e v) ∧ ∃ e' ∉ U, G.Inc e' v} := by
  sorry

end IsVxSetSeparator



def IsEdgeSetSeparator (G : Graph α β) (S T : Set α) (F : Set β) :=
  ¬ (G \ F).SetConnected S T

namespace IsEdgeSetSeparator
variable {G G' : Graph α β} {S S' T T' : Set α} {F F' : Set β} {u v : α} {w : Walk α β}

-- Basic Properties & Negation
@[simp] lemma not_isEdgeSetSeparator_iff : ¬ G.IsEdgeSetSeparator S T F ↔ (G.edgeDel F).SetConnected S T := by
  simp [IsEdgeSetSeparator]

lemma symm (h : G.IsEdgeSetSeparator S T F) : G.IsEdgeSetSeparator T S F := by
  simp only [IsEdgeSetSeparator, SetConnected.comm] at h ⊢
  exact h

lemma comm : G.IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator T S F :=
  ⟨symm, symm⟩

-- Monotonicity & Subsets
lemma le (h : G'.IsEdgeSetSeparator S T F) (hle : G ≤ G') : G.IsEdgeSetSeparator S T F :=
  fun hconn ↦ h <| hconn.le (edgeDel_le_edgeDel_of_subset hle fun ⦃_⦄ a ↦ a)

lemma mono (h : G.IsEdgeSetSeparator S T F) (h_subset : F ⊆ F') :
    G.IsEdgeSetSeparator S T F' := by
  refine fun hconn ↦ h ?_
  refine hconn.le (edgeDel_le_edgeDel_of_subset (le_refl G) h_subset)

@[simp]
lemma subset_source (h : G.IsEdgeSetSeparator S' T F) (hS : S ⊆ S') : G.IsEdgeSetSeparator S T F :=
  fun hconn ↦ h <| hconn.left_subset hS

@[simp]
lemma subset_target (h : G.IsEdgeSetSeparator S T' F) (hT : T ⊆ T') : G.IsEdgeSetSeparator S T F :=
  fun hconn ↦ h <| hconn.right_subset hT

-- Empty and Universal Sets
@[simp]
lemma empty_iff : G.IsEdgeSetSeparator S T ∅ ↔ ¬ G.SetConnected S T := by
  simp [IsEdgeSetSeparator]

@[simp] lemma empty_source : G.IsEdgeSetSeparator ∅ T F := by
  simp [IsEdgeSetSeparator]

@[simp] lemma empty_target : G.IsEdgeSetSeparator S ∅ F := by
  simp [IsEdgeSetSeparator]

@[simp] lemma edge_univ_sep : G.IsEdgeSetSeparator S T univ ↔ S ∩ T ∩ G.V = ∅ := by
  simp [IsEdgeSetSeparator, not_nonempty_iff_eq_empty]

@[simp] lemma edge_support_sep : G.IsEdgeSetSeparator S T G.E ↔ S ∩ T ∩ G.V = ∅ := by
  simp [IsEdgeSetSeparator, not_nonempty_iff_eq_empty]

-- Support & Interaction with Graph Structure
lemma sep_support : G.IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator S T (F ∩ G.E) := by
  simp [IsEdgeSetSeparator]
  suffices G \ F = G \ (F ∩ G.E) by rw [this]
  rw [edgeDel_eq_edgeDel_iff]
  simp

lemma left_support : G.IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator (S ∩ G.V) T F := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.left_supported] at hconn ⊢
    exact hconn.left_subset (by tauto_set)
  · rw [SetConnected.left_supported] at hconn
    exact hconn.left_subset (by tauto_set)

lemma right_support : G.IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator S (T ∩ G.V) F := by
  constructor <;> refine fun hSep hconn ↦ hSep ?_
  · rw [SetConnected.right_supported] at hconn ⊢
    exact hconn.right_subset (by tauto_set)
  · rw [SetConnected.right_supported] at hconn
    exact hconn.right_subset (by tauto_set)

lemma left_right_support : G.IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator (S ∩ G.V) (T ∩ G.V) F := by
  rw [left_support, right_support]

-- Composition
@[simp]
lemma edgeDel : (G \ F').IsEdgeSetSeparator S T F ↔ G.IsEdgeSetSeparator S T (F' ∪ F) := by
  simp [IsEdgeSetSeparator]

end IsEdgeSetSeparator


lemma vxDel_isEdgeSetSeparator_iff_edgeDel_isVxSetSeparator :
    (G - U).IsEdgeSetSeparator S T F ↔ (G \ F).IsVxSetSeparator S T U := by
  unfold IsEdgeSetSeparator IsVxSetSeparator
  rw [vxDel_edgeDel_comm]

-- Relationship with Vertex Separators
def IncidenceEdges (G : Graph α β) (V : Set α) : Set β := {e ∈ G.E | ∃ v ∈ V, G.Inc e v}
def IncidentVertices (G : Graph α β) (F : Set β) : Set α := {v ∈ G.V | ∃ e ∈ F, G.Inc e v}

lemma vxSep_implies_edgeSep (h : G.IsVxSetSeparator U S T) :
    G.IsEdgeSetSeparator S T (IncidenceEdges G U) := by

  sorry

lemma edgeSep_implies_vxSep (h : G.IsEdgeSetSeparator S T F) :
    G.IsVxSetSeparator (IncidentVertices G F) S T := by
  sorry

end Graph
