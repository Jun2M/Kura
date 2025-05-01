import Kura.Operation.MapHom
import Kura.Walk.Path

open Set Function
variable {α α' α'' β β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

/- I have been thinking about a way to `contract` without supplying the vx map but just the edge
set I am contracting on. This is one way to do it using partitions. -/

def IsPartitionGraph (G : Graph (Set α) β) : Prop :=
  ∃ P : Partition (Set α), P.parts = G.V

def Setify (G : Graph α β) : Graph (Set α) β :=
  vxMap G ({·})

def Setify.HasIsom (G : Graph α β) : G ≤↔ G.Setify :=
  vxMap.HasIsom ({·}) singleton_injective.injOn

lemma Setify.IsPartitionGraph (G : Graph α β) : G.Setify.IsPartitionGraph := by
  use Partition.discrete G.V
  simp only [Partition.discrete.parts, Setify, vxMap.V]

def SetContract (G : Graph (Set α) β) (C : Set β) : Graph (Set α) β :=
  G.vxMap (⋃₀ G{C}.Component ·) \ C

scoped infix:100 " / " => Graph.SetContract

variable {G : Graph (Set α) β} {C D : Set β}

@[simp]
lemma SetContract.V : (G / C).V = (⋃₀ G{C}.Component ·) '' G.V := rfl

@[simp]
lemma SetContract.E : (G / C).E = G.E \ C := by
  simp [SetContract]

@[simp]
lemma SetContract.toMultiset (heC : e ∉ C) :
    (G / C).toMultiset e = (G.toMultiset e).map (⋃₀ G{C}.Component ·) := by
  simp [SetContract]
  rw [← vxMap_toMultiset_eq_map_toMultiset, toMultiset_eq_toMultiset]
  ext x y
  simp [heC]

@[simp]
lemma SetContract.Inc {u : Set α} :
    (G / C).Inc e u ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ ⋃₀ G{C}.Component v = u := by
  simp only [SetContract, edgeDel_inc, vxMap_inc_iff]
  tauto

@[simp]
lemma SetContract.Inc₂ {u v : Set α} :
    (G / C).Inc₂ e u v ↔ e ∉ C ∧ ∃ x y, G.Inc₂ e x y ∧ ⋃₀ G{C}.Component x = u ∧ ⋃₀ G{C}.Component y = v := by
  simp only [SetContract, edgeDel_inc₂, vxMap_inc₂_iff]
  tauto

lemma SetContract.subset_map (C : Set β) {u : Set α} (hu : u ∈ G.V) : u ⊆ ⋃₀ G{C}.Component u :=
  subset_sUnion_of_subset (G{C}.Component u) u (fun _ a ↦ a) (Connected.refl hu)

lemma SetContract.map_eq_iff' {u v : Set α} (hP : G.IsPartitionGraph) (hv : v ∈ G.V) :
    ⋃₀ G{C}.Component u = ⋃₀ G{C}.Component v ↔ G{C}.Connected u v := by
  obtain ⟨P, hP⟩ := hP
  rw [← hP] at hv
  constructor <;> intro h
  · have : v ⊆ ⋃₀ G{C}.Component v := subset_map C (hP ▸ hv)
    rw [← h, P.subset_sUnion_iff_mem hv (by rw [hP, ← restrict_V (R := C)]; exact Component.subset_V)] at this
    simpa using this
  · ext x
    simp only [mem_sUnion, Component.mem]
    have : ∀ t, G{C}.Connected u t ↔ G{C}.Connected v t := fun _ ↦ rel_congr_left h
    simp_rw [this]

lemma SetContract.map_eq_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ G.V) :
    ⋃₀ G{C}.Component u = ⋃₀ G{C}.Component v ↔ G{C}.Connected u v := by
  rw [eq_comm, Connected.comm, SetContract.map_eq_iff' hP hu]

@[simp]
lemma SetContract.map_mem_iff {u : Set α} (hP : G.IsPartitionGraph) :
    (⋃₀ G{C}.Component u) ∈ (G / C).V ↔ u ∈ G.V := by
  simp only [V, mem_image]
  constructor <;> rintro h
  · obtain ⟨x, hx, heq⟩ := h
    rw [map_eq_iff hP hx] at heq
    exact heq.mem_right
  · use u

-- @[simp]
-- lemma SetContract.merged_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ G.V) (hv : v ∈ G.V) :
--     (∃ x ∈ (G / C).V, u ⊆ x ∧ v ⊆ x) ↔ G{C}.Connected u v := by
--   obtain ⟨P, hP⟩ := hP
--   constructor
--   · rintro ⟨x, hx, hux, hvx⟩
--     simp only [V, mem_image] at hx
--     obtain ⟨S, hS, rfl⟩ := hx
--     rw [← hP] at hS hu hv
--     simp only [Component] at hux hvx
--     exact ((P.subset_sUnion_iff_mem hu (hP ▸ fun x hx ↦ (by
--       simpa using hx : G{C}.Connected S x).mem_right)).mp hux).symm.trans
--       ((P.subset_sUnion_iff_mem hv (hP ▸ fun x hx ↦ (by
--       simpa using hx : G{C}.Connected S x).mem_right)).mp hvx)
--   · intro h
--     use ⋃₀ G{C}.Component u, (by use u), ?_
--     · exact subset_sUnion_of_subset (G{C}.Component u) v (fun ⦃a⦄ a ↦ a) h
--     · exact subset_sUnion_of_subset (G{C}.Component u) u (fun ⦃a⦄ a ↦ a) (Connected.refl hu)

lemma SetContract.IsPartitionGraph (C : Set β) (hP : G.IsPartitionGraph) :
    (G / C).IsPartitionGraph := by
  obtain ⟨P, hP⟩ := hP
  use G{C}.ConnectedPartition.flatten ⟨P, by simp [hP]⟩
  simp only [Partition.flatten_parts, sSup_eq_sUnion, ConnectedPartition.parts, ComponentSets,
    restrict_V, V]
  rw [image_image]

lemma setContract_edgeDel_comm (G : Graph (Set α) β) (hCD : Disjoint C D) :
    (G / C) \ D = (G \ D) / C := by
  have heq : G{C} = (G \ D){C} := by
    rw [edgeDel, restrict_restrict_eq_restrict_inter, restrict_eq_restrict_iff]
    tauto_set
  refine ext_inc₂ ?_ fun e x y ↦ ?_
  · ext u
    simp only [edgeDel_V, SetContract.V, mem_image, heq]
  · simp only [edgeDel_inc₂, SetContract.Inc₂, ← heq]
    tauto

lemma SetContract.foo {u v : Set α} (hP : G.IsPartitionGraph)
    (hTconn : (G / C){D}.Connected (⋃₀ G{C}.Component v) (⋃₀ G{C}.Component u)) :
    G{C ∪ D}.Connected v u := by
  have hu : u ∈ G.V := (SetContract.map_mem_iff hP).mp hTconn.mem_right
  have hv : v ∈ G.V := (SetContract.map_mem_iff hP).mp hTconn.mem_left
  obtain ⟨w, hwVd, hwfst, hwlst⟩ := connected_iff_exists_walk.mp hTconn ; clear hTconn
  induction w generalizing v with
  | nil v =>
    simp only [WList.nil_first, WList.nil_last] at hwfst hwlst
    rw [hwfst, map_eq_iff' hP hu] at hwlst
    exact hwlst.of_le (restrict_mono G subset_union_left)
  | cons a e w ih =>
    simp only [WList.first_cons, WList.last_cons, cons_isWalk_iff, restrict_inc₂_iff,
      Inc₂] at hwfst hwlst hwVd
    obtain ⟨⟨⟨heC, x, y, hbtw, rfl, hy⟩, heD⟩, hwVd⟩ := hwVd
    rw [map_eq_iff' hP hv] at hwfst
    exact hwfst.symm.of_le (restrict_mono G subset_union_left)
    |>.trans (restrict_inc₂_iff.mpr ⟨hbtw, by tauto⟩).connected
    |>.trans (ih hbtw.vx_mem_right hwVd hy.symm hwlst)

lemma SetContract.foo2 {u v : Set α} (hP : G.IsPartitionGraph) (h : G{C ∪ D}.Connected v u) :
    (G / C){D}.Connected (⋃₀ G{C}.Component v) (⋃₀ G{C}.Component u) := by
  obtain ⟨w, hwVd, rfl, rfl⟩ := connected_iff_exists_walk.mp h ; clear h
  induction w with
  | nil x =>
    simp only [WList.nil_last, WList.nil_first, Connected.refl_iff, restrict_V, V,
      mem_image]
    use x, by simpa using hwVd
  | cons a e w ih =>
    simp only [cons_isWalk_iff, restrict_inc₂_iff, mem_union, WList.last_cons,
      WList.first_cons] at hwVd ⊢
    obtain ⟨⟨hbtw, he⟩, hwVd⟩ := hwVd
    by_cases heC : e ∈ C <;> refine Connected.trans ?_ (ih hwVd)
    · convert Connected.refl ?_ using 1
      · rw [map_eq_iff' hP hbtw.vx_mem_left]
        exact (restrict_inc₂_iff.mpr ⟨hbtw.symm, heC⟩).connected
      · use a, hbtw.vx_mem_left
    · simp only [heC, false_or] at he
      refine Inc₂.connected ?_ (e := e)
      simp only [restrict_inc₂_iff, Inc₂, heC, not_false_eq_true, true_and, he, and_true]
      use a, w.first

lemma SetContract.map_map (C D : Set β) (hP : G.IsPartitionGraph) {v : Set α}  :
    ⋃₀ (G / C){D}.Component (⋃₀ G{C}.Component v) = ⋃₀ G{C ∪ D}.Component v := by
  ext x
  simp only [mem_sUnion, Component.mem]
  constructor
  · rintro ⟨T, hTconn, hxT⟩
    obtain ⟨u, hu, rfl⟩ := hTconn.mem_right
    obtain ⟨u', hu'conn, hxu'⟩ := hxT
    use u', (foo hP hTconn).trans (hu'conn.of_le (restrict_mono G subset_union_left))
  · rintro ⟨u, huconn, hxu⟩
    use ⋃₀ G{C}.Component u, foo2 hP huconn
    refine subset_map C ?_ hxu
    exact huconn.mem_right

lemma SetContract.contract_contract (C D : Set β) (hP : G.IsPartitionGraph) :
    (G / C) / D = G / (C ∪ D) := by
  refine ext_inc₂ ?_ fun e x y ↦ ?_
  · ext u
    simp only [V, mem_image, exists_exists_and_eq_and, map_map C D hP]
  · simp only [Inc₂, mem_union, not_or]
    constructor
    · rintro ⟨heD, _, _, ⟨heC, x, y, hbtw, rfl, rfl⟩, rfl, rfl⟩
      simp only [heC, not_false_eq_true, heD, and_self, map_map C D hP, true_and]
      use x, y
    · rintro ⟨⟨heC, heD⟩, x, y, hbtw, rfl, rfl⟩
      simp only [heD, not_false_eq_true, heC, true_and]
      use ⋃₀ G{C}.Component x, ⋃₀ G{C}.Component y, (by use x, y), map_map C D hP, map_map C D hP




end Graph
