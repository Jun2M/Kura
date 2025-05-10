import Kura.Operation.MapHom


open Set Function
variable {α β α' α'' β' : Type*} {G H : Graph (Set α) β} {a b c : α} {x y z : Set α} {e f : β}

namespace Graph

/- I have been thinking about a way to `contract` without supplying the vx map but just the edge
set I am contracting on. This is one way to do it using partitions. -/

def IsPartitionGraph [CompleteLattice α] (G : Graph α β) : Prop :=
  ∃ P : Partition α, P.parts = G.V

instance instIsPartitionGraphGraphicVertex : GraphicVertexFunction (fun {β} (G : Graph (Set α) β) ↦
  G.IsPartitionGraph) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    rw [eq_iff_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨P, hP⟩ := h
      use P
      rw [hP]
      simpa only [HomSys.ofEdgeFun, _root_.bijOn_id] using hf.bijOn_vx
    · obtain ⟨P, hP⟩ := h
      use P
      rw [hP, eq_comm]
      simpa only [HomSys.ofEdgeFun, _root_.bijOn_id] using hf.bijOn_vx

def Setify (G : Graph α β) : Graph (Set α) β :=
  vxMap G ({·})

def Setify.HasIsom (G : Graph α β) : G ≤↔ G.Setify :=
  vxMap.HasIsom ({·}) singleton_injective.injOn

lemma Setify.IsPartitionGraph (G : Graph α β) : G.Setify.IsPartitionGraph := by
  use Partition.discrete G.V
  ext x
  simp [Partition.discrete, Setify]
  refine exists_congr fun a => and_congr_right fun ha => ?_
  revert x
  rw [eq_iff_eq_cancel_right]
  simp [ha]

@[simps! vxSet edgeSet]
def VxIdentification (G : Graph (Set α) β) (P : Partition (Set (Set α))) :
    Graph (Set α) β :=
  G.vxMap (⋃₀ P.partOf ·)

variable {P : Partition (Set (Set α))} (hP : ⋃₀ P.parts = G.V)

@[simp]
lemma vxIdentification_inc₂ : (G.VxIdentification P).Inc₂ e x y ↔ ∃ x' y',
    G.Inc₂ e x' y' ∧ ⋃₀ P.partOf x' = x ∧ ⋃₀ P.partOf y' = y := by
  rw [VxIdentification, vxMap_inc₂]

lemma vxIdentification_inc₂_toMultiset :
    (G.VxIdentification P).Inc₂ e x y ↔ (G.toMultiset e).map (⋃₀ P.partOf ·) = {x, y} := by
  rw [VxIdentification, vxMap_inc₂_toMultiset]

@[simp]
lemma vxIdentification_toMultiset :
    (G.VxIdentification P).toMultiset e = (G.toMultiset e).map (⋃₀ P.partOf ·) := by
  rw [VxIdentification, vxMap_toMultiset]

@[simp]
lemma vxIdentification_inc : (G.VxIdentification P).Inc e x ↔ ∃ y, G.Inc e y ∧ ⋃₀ P.partOf y = x := by
  rw [VxIdentification, vxMap_inc]
