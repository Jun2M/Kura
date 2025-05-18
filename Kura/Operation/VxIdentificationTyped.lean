import Kura.Operation.MapHom
import Matroid.ForMathlib.SetPartition

open Set Function
variable {α β α' α'' β' : Type*} {G H : Graph (Set α) β} {a b c : α} {x y z : Set α} {e f : β}

namespace Graph

/- I have been thinking about a way to `contract` without supplying the vx map but just the edge
set I am contracting on. This is one way to do it using partitions. -/

def IsPartitionGraph (G : Graph (Set α) β) : Prop :=
  ∃ P : Partition (⋃₀ V(G)), P.parts = V(G)

def Setify (G : Graph α β) : Graph (Set α) β :=
  vxMap G ({·})

def Setify.HasIsom (G : Graph α β) : G ≤↔ G.Setify :=
  vxMap.HasIsom ({·}) singleton_injective.injOn

lemma Setify.IsPartitionGraph (G : Graph α β) : G.Setify.IsPartitionGraph := by
  use (Partition.discrete V(G)).congr (by simp [Setify])
  ext x
  simp [Partition.discrete, Setify]
  refine exists_congr fun a => and_congr_right fun ha => ?_
  revert x
  rw [eq_iff_eq_cancel_right]
  simp [ha]

@[simps! vertexSet edgeSet]
def VxIdentification (G : Graph (Set α) β) (P : Partition V(G)) : Graph (Set α) β :=
  G.vxMap (⋃₀ P.partOf ·)

variable {P : Partition V(G)}

@[simp]
lemma vxIdentification_isLink : (V(G)xIdentification P).IsLink e x y ↔ ∃ x' y',
    G.IsLink e x' y' ∧ ⋃₀ P.partOf x' = x ∧ ⋃₀ P.partOf y' = y := by
  rw [VxIdentification, vxMap_isLink]

lemma vxIdentification_isLink_toMultiset :
    (V(G)xIdentification P).IsLink e x y ↔ (G.toMultiset e).map (⋃₀ P.partOf ·) = {x, y} := by
  rw [VxIdentification, vxMap_isLink_toMultiset]

@[simp]
lemma vxIdentification_toMultiset :
    (V(G)xIdentification P).toMultiset e = (G.toMultiset e).map (⋃₀ P.partOf ·) := by
  rw [VxIdentification, vxMap_toMultiset]

@[simp]
lemma vxIdentification_inc : (V(G)xIdentification P).Inc e x ↔ ∃ y, G.Inc e y ∧ ⋃₀ P.partOf y = x := by
  rw [VxIdentification, vxMap_inc]


structure IdentifyingMap {G : Graph (Set α) β} (P : Partition V(G)) where
  toFun : Set α → Set α
  eq_preimg_sUnion : ∀ p ∈ V(G), toFun p = ⋃₀ (toFun ⁻¹' {toFun p})

lemma IdentifyingMap.fiber {G : Graph (Set α) β} (P : Partition V(G)) (f : IdentifyingMap P) :
    G.vxMap f.toFun = V(G)xIdentification P := by
  unfold VxIdentification
  sorry
