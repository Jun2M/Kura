import Kura.Operation.Hom
import Kura.Dep.SetPartitionTypeless


open Set Function
variable {α β α' α'' β' : Type*} {G H : Graph (Set α) β} {a b c : α} {x y z : Set α} {e f : β}

namespace Graph

/- I have been thinking about a way to `contract` without supplying the vx map but just the edge
set I am contracting on. This is one way to do it using partitions. -/

def IsPartitionGraph [CompleteLattice α] (G : Graph α β) : Prop :=
  ∃ P : Partition α, P.parts = V(G)

instance instIsPartitionGraphGraphicVertex [CompleteLattice α] :
    GraphicVertexFunction (Graph.IsPartitionGraph (α := α)) (Graph.IsPartitionGraph) where
  invariant h := by
    obtain ⟨f, hf⟩ := h
    rw [eq_iff_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    · obtain ⟨P, hP⟩ := h
      use P
      rw [hP, instVxSetGraphicVertex.invariant ⟨f, hf⟩]


@[simps!]
noncomputable def Setify (G : Graph α β) : Graph (Set α) β :=
  vxMap G ({·})

def setify_hasIsom (G : Graph α β) : G ↔ᴳ G.Setify :=
  vxMap_hasIsom singleton_injective.injOn

lemma setify_isPartitionGraph (G : Graph α β) : G.Setify.IsPartitionGraph := by
  use Partition.discrete V(G)
  ext x
  simp [Partition.discrete, Setify]
  refine exists_congr fun a => and_congr_right fun ha => ?_
  revert x
  rw [eq_iff_eq_cancel_right]
  simp [ha]

lemma forall_setify (F : {α : Type _} → {β : Type _} → Graph α β → Prop)
    [hF : GraphicFunction F F] (h : ∀ (G' : Graph (Set α) β), G'.IsPartitionGraph → F G') :
    ∀ (G : Graph α β), F G := fun G => by
    rw [hF.invariant (setify_hasIsom G)]
    exact h G.Setify <| setify_isPartitionGraph G


@[simps! vertexSet edgeSet]
noncomputable def VxIdentification (G : Graph (Set α) β) (P : Partition (Set (Set α))) :
    Graph (Set α) β :=
  G.vxMap (⋃₀ P.partOf ·)

variable {P : Partition (Set (Set α))}

@[simp]
lemma vxIdentification_isLink : (G.VxIdentification P).IsLink e x y ↔ ∃ x', ⋃₀ P.partOf x' = x ∧
  ∃ y', ⋃₀ P.partOf y' = y ∧ G.IsLink e x' y' := by
  rw [VxIdentification, vxMap_isLink]

lemma vxIdentification_isLink_toMultiset :
    (G.VxIdentification P).IsLink e x y ↔ (G.toMultiset e).map (⋃₀ P.partOf ·) = {x, y} := by
  rw [VxIdentification, vxMap_isLink_toMultiset]

@[simp]
lemma vxIdentification_toMultiset :
    (G.VxIdentification P).toMultiset e = (G.toMultiset e).map (⋃₀ P.partOf ·) := by
  rw [VxIdentification, vxMap_toMultiset]

@[simp]
lemma vxIdentification_inc : (G.VxIdentification P).Inc e x ↔ ∃ y, G.Inc e y ∧ ⋃₀ P.partOf y = x := by
  rw [VxIdentification, vxMap_inc]

lemma vxIdentification_isPartitionGraph (hP : P.supp = V(G)) (hGP : G.IsPartitionGraph) :
    (G.VxIdentification P).IsPartitionGraph := by
  obtain ⟨P', hP'⟩ := hGP
  use P.flatten ⟨P', hP'.trans hP.symm⟩
  ext v
  simp only [Partition.flatten_parts, sSup_eq_sUnion, mem_image, Partition.mem_parts,
    SetLike.mem_coe, VxIdentification_vertexSet]
  refine ⟨fun ⟨x, hx, hv⟩ => ?_, fun ⟨x, hx, hv⟩ => ?_⟩ <;> subst v
  · obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr <| P.ne_bot_of_mem hx
    use v, hP ▸ mem_sUnion_of_mem hv hx, by rw [P.eq_partOf_of_mem hx hv]
  · use P.partOf x, P.partOf_mem (hP ▸ hx)


noncomputable def VxIdenBySet (G : Graph (Set α) β) (S : Set (Set α)) : Graph (Set α) β :=
  G.VxIdentification (Partition.indiscrete' (V(G) ∩ S) ⊔ Partition.discrete (V(G) \ S))

scoped infix:100 " ÷ " => VxIdenBySet

variable {G : Graph (Set α) β} {S : Set (Set α)}

@[simp]
lemma vxIdenBySet_isPartitionGraph (hGP : G.IsPartitionGraph) : (G ÷ S).IsPartitionGraph := by
  rw [VxIdenBySet]
  apply vxIdentification_isPartitionGraph (by simp) hGP

@[simp]
lemma vxIdenBySet_vertexSet : V(G ÷ S) = (V(G) \ S) ∪ {⋃₀ S} := by
  ext s
  simp only [VxIdenBySet, VxIdentification_vertexSet, mem_image, union_singleton, mem_insert_iff,
    mem_diff]
  sorry

@[simp]
lemma vxIdenBySet_edgeSet : E(G ÷ S) = E(G) := by
  simp [VxIdenBySet]

@[simp]
lemma vxIdenBySet_isLink : (G ÷ S).IsLink e x y ↔ ∃ x', (x' ∈ S → x = ⋃₀ (V(G) ∩ S)) ∧ ∃ y',
    (y' ∈ S → y = ⋃₀ (V(G) ∩ S)) ∧ G.IsLink e x' y' := by
  simp [VxIdenBySet]
  congr!
  · rename_i s
    refine ⟨fun h hsS => ?_, fun h => ?_⟩
    · subst x
      congr!
      rw [Partition.partOf_sup_eq_of_disjoint]
      sorry
      sorry
      sorry
    · sorry
  · rename_i s t
    sorry
