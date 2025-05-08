import Kura.Operation.VxIdentification
import Kura.Connected

open Set Function
variable {α ε α' α'' ε' : Type*} {G G' H H' : Graph α ε} {u v w : α} {e f : ε} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set ε}
namespace Graph

def SetContract (G : Graph (Set α) ε) (C : Set ε) : Graph (Set α) ε :=
  G.VxIdentification (G ↾ C).ConnectivityPartition ＼ C

-- scoped infix:70 " / " => Graph.SetContract

instance : HDiv (Graph (Set α) ε) (Set ε) (Graph (Set α) ε) where
  hDiv := SetContract

def setContract_def (G : Graph (Set α) ε) (C : Set ε) : G / C = G.SetContract C := rfl

@[simp]
lemma setContract_vxSet (G : Graph (Set α) ε) (C : Set ε) :
  (G / C).V = (⋃₀ (G ↾ C).Component · ) '' G.V := by
  rw [← connectivityPartition_partOf]
  rfl

@[simp]
lemma SetContract_edgeSet (G : Graph (Set α) ε) (C : Set ε) : (G / C).E = G.E \ C :=
  congrArg (· \ C) (VxIdentification_edgeSet G _)

@[simp]
lemma SetContract_inc₂ (G : Graph (Set α) ε) (C : Set ε) (e : ε) (x y : Set α) :
    (G / C).Inc₂ e x y ↔ (e ∉ C ∧ ∃ x' y', G.Inc₂ e x' y' ∧ ⋃₀ (G ↾ C).Component x' = x ∧ ⋃₀ (G ↾ C).Component y' = y) := by
  rw [← connectivityPartition_partOf, setContract_def, SetContract, edgeDelete_inc₂,
    vxIdentification_inc₂]

variable {G : Graph (Set α) ε} {C D : Set ε}

@[simp]
lemma setContract_toMultiset (heC : e ∉ C) :
    (G / C).toMultiset e = (G.toMultiset e).map (⋃₀ (G ↾ C).Component ·) := by
  simp [SetContract, ← connectivityPartition_partOf]
  rw [← vxMap_toMultiset, toMultiset_eq_toMultiset_iff]
  ext x y
  simp [heC]

@[simp]
lemma setContract_inc {u : Set α} :
    (G / C).Inc e u ↔ e ∉ C ∧ (∃ v, G.Inc e v ∧ ⋃₀ (G ↾ C).Component v = u) := by
  simp_rw [setContract_def, SetContract, ← connectivityPartition_partOf, inc_iff_exists_inc₂,
    edgeDelete_inc₂, exists_and_left, ← inc_iff_exists_inc₂, vxIdentification_inc]

@[simp]
lemma setContract_inc₂ {u v : Set α} : (G / C).Inc₂ e u v ↔
    e ∉ C ∧ (∃ x y, G.Inc₂ e x y ∧ ⋃₀ (G ↾ C).Component x = u ∧ ⋃₀ (G ↾ C).Component y = v) := by
  simp_rw [setContract_def, SetContract, ← connectivityPartition_partOf, edgeDelete_inc₂,
    vxIdentification_inc₂]

lemma SetContract.subset_map (C : Set ε) {u : Set α} (hu : u ∈ G.V) : u ⊆ ⋃₀ (G ↾ C).Component u :=
  subset_sUnion_of_subset ((G ↾ C).Component u) u (fun _ a ↦ a) (VxConnected.refl hu)

lemma SetContract.map_eq_iff' {u v : Set α} (hP : G.IsPartitionGraph) (hv : v ∈ G.V) :
    ⋃₀ (G ↾ C).Component u = ⋃₀ (G ↾ C).Component v ↔ (G ↾ C).VxConnected u v := by
  obtain ⟨P, hP⟩ := hP
  rw [← hP] at hv
  constructor <;> intro h
  · have : v ⊆ ⋃₀ (G ↾ C).Component v := subset_map C (hP ▸ hv)
    rw [← h, P.subset_sUnion_iff_mem hv (by rw [hP, ← edgeRestrict_vxSet]; exact component_subset_V)] at this
    simpa using this
  · ext x
    simp only [mem_sUnion, mem_component_iff]
    have : ∀ t, (G ↾ C).VxConnected u t ↔ (G ↾ C).VxConnected v t := fun _ ↦ rel_congr_left h
    simp_rw [this]

lemma SetContract.map_eq_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ G.V) :
    ⋃₀ (G ↾ C).Component u = ⋃₀ (G ↾ C).Component v ↔ (G ↾ C).VxConnected u v := by
  rw [eq_comm, vxConnected_comm, SetContract.map_eq_iff' hP hu]

@[simp]
lemma SetContract.map_mem_iff {u : Set α} (hP : G.IsPartitionGraph) :
    (⋃₀ (G ↾ C).Component u) ∈ (G / C).V ↔ u ∈ G.V := by
  simp only [setContract_vxSet, mem_image]
  constructor <;> rintro h
  · obtain ⟨x, hx, heq⟩ := h
    rw [map_eq_iff hP hx] at heq
    exact heq.mem_right
  · use u

-- @[simp]
-- lemma SetContract.merged_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ G.V) (hv : v ∈ G.V) :
--     (∃ x ∈ (G / C).V, u ⊆ x ∧ v ⊆ x) ↔ (G ↾ C).Connected u v := by
--   obtain ⟨P, hP⟩ := hP
--   constructor
--   · rintro ⟨x, hx, hux, hvx⟩
--     simp only [V, mem_image] at hx
--     obtain ⟨S, hS, rfl⟩ := hx
--     rw [← hP] at hS hu hv
--     simp only [Component] at hux hvx
--     exact ((P.subset_sUnion_iff_mem hu (hP ▸ fun x hx ↦ (by
--       simpa using hx : (G ↾ C).Connected S x).mem_right)).mp hux).symm.trans
--       ((P.subset_sUnion_iff_mem hv (hP ▸ fun x hx ↦ (by
--       simpa using hx : (G ↾ C).Connected S x).mem_right)).mp hvx)
--   · intro h
--     use ⋃₀ (G ↾ C).Component u, (by use u), ?_
--     · exact subset_sUnion_of_subset ((G ↾ C).Component u) v (fun ⦃a⦄ a ↦ a) h
--     · exact subset_sUnion_of_subset ((G ↾ C).Component u) u (fun ⦃a⦄ a ↦ a) (Connected.refl hu)

lemma SetContract.IsPartitionGraph (C : Set ε) (hP : G.IsPartitionGraph) :
    (G / C).IsPartitionGraph := by
  obtain ⟨P, hP⟩ := hP
  use (G ↾ C).ConnectivityPartition.flatten (by use P; simp [hP])
  simp only [Partition.flatten_parts, sSup_eq_sUnion, connectedPartition_parts, ComponentSets,
    edgeRestrict_vxSet, setContract_vxSet, connectivityPartition_partOf]
  rw [image_image]

lemma setContract_edgeDel_comm (G : Graph (Set α) ε) (hCD : Disjoint C D) :
    G / C ＼ D = (G ＼ D) / C := by
  have heq : (G ↾ C) = (G ＼ D) ↾ C := by
    rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_eq_edgeRestrict_iff]
    tauto_set
  refine ext_inc ?_ fun e x ↦ ?_
  · ext u
    simp only [edgeDelete_vxSet, setContract_vxSet, heq, mem_image]
  · simp only [edgeDelete_inc, setContract_inc, ← heq]
    tauto

lemma SetContract.foo {u v : Set α} (hP : G.IsPartitionGraph)
    (hTconn : (G / C ↾ D).VxConnected (⋃₀ (G ↾ C).Component v) (⋃₀ (G ↾ C).Component u)) :
    (G ↾ (C ∪ D)).VxConnected v u := by
  have hu : u ∈ G.V := (SetContract.map_mem_iff hP).mp hTconn.mem_right
  have hv : v ∈ G.V := (SetContract.map_mem_iff hP).mp hTconn.mem_left
  obtain ⟨w, hwVd, hwfst, hwlst⟩ := vxConnected_iff_exists_walk.mp hTconn ; clear hTconn
  induction w generalizing v with
  | nil v =>
    simp only [WList.nil_first, WList.nil_last] at hwfst hwlst
    rw [hwfst, map_eq_iff' hP hu] at hwlst
    exact hwlst.of_le (edgeRestrict_mono_right G subset_union_left)
  | cons a e w ih =>
    simp only [WList.first_cons, WList.last_cons, cons_isWalk_iff, edgeRestrict_inc₂,
      setContract_inc₂] at hwfst hwlst hwVd
    obtain ⟨⟨heD, heC, x, y, hbtw, rfl, hy⟩, hwVd⟩ := hwVd
    rw [map_eq_iff' hP hv] at hwfst
    exact hwfst.symm.of_le (edgeRestrict_mono_right G subset_union_left)
    |>.trans ((edgeRestrict_inc₂ _ _ _ _ _).mpr ⟨by tauto, hbtw⟩).vxConnected
    |>.trans (ih hbtw.vx_mem_right hwVd hy.symm hwlst)

lemma SetContract.foo2 {u v : Set α} (hP : G.IsPartitionGraph) (h : (G ↾ (C ∪ D)).VxConnected v u) :
    (G / C ↾ D).VxConnected (⋃₀ (G ↾ C).Component v) (⋃₀ (G ↾ C).Component u) := by
  obtain ⟨w, hwVd, rfl, rfl⟩ := vxConnected_iff_exists_walk.mp h ; clear h
  induction w with
  | nil x =>
    simp only [WList.nil_last, WList.nil_first, vxConnected_self, edgeRestrict_vxSet, V,
      mem_image]
    use x, by simpa using hwVd
    rw [connectivityPartition_partOf]
  | cons a e w ih =>
    simp only [cons_isWalk_iff, edgeRestrict_inc₂, mem_union, WList.last_cons,
      WList.first_cons] at hwVd ⊢
    obtain ⟨⟨he, hbtw⟩, hwVd⟩ := hwVd
    by_cases heC : e ∈ C <;> refine VxConnected.trans ?_ (ih hwVd)
    · convert VxConnected.refl ?_ using 1
      · rw [map_eq_iff' hP hbtw.vx_mem_left]
        exact ((edgeRestrict_inc₂ _ _ _ _ _).mpr ⟨heC, hbtw.symm⟩).vxConnected
      · use a, hbtw.vx_mem_left
        rw [connectivityPartition_partOf]
    · simp only [heC, false_or] at he
      refine Inc₂.vxConnected ?_ (e := e)
      simp only [edgeRestrict_inc₂, he, setContract_inc₂, heC, not_false_eq_true, true_and]
      use a, w.first

lemma SetContract.map_map (C D : Set ε) (hP : G.IsPartitionGraph) {v : Set α}  :
    ⋃₀ (G / C ↾ D).Component (⋃₀ (G ↾ C).Component v) = ⋃₀ (G ↾ (C ∪ D)).Component v := by
  ext x
  simp only [mem_sUnion, mem_component_iff]
  constructor
  · rintro ⟨T, hTconn, hxT⟩
    obtain ⟨u, hu, rfl⟩ := hTconn.mem_right
    obtain ⟨u', hu'conn, hxu'⟩ := hxT
    rw [connectivityPartition_partOf] at hTconn hu'conn
    use u', (foo hP hTconn).trans (hu'conn.of_le (edgeRestrict_mono_right G subset_union_left))
  · rintro ⟨u, huconn, hxu⟩
    use ⋃₀ (G ↾ C).Component u, foo2 hP huconn
    refine subset_map C ?_ hxu
    exact huconn.mem_right

lemma SetContract.contract_contract (C D : Set ε) (hP : G.IsPartitionGraph) :
    (G / C) / D = G / (C ∪ D) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · ext u
    simp only [setContract_vxSet, mem_image, exists_exists_and_eq_and, map_map C D hP]
  · simp only [setContract_inc₂, mem_union, not_or]
    constructor
    · rintro ⟨heD, _, _, ⟨heC, x, y, hbtw, rfl, rfl⟩, rfl, rfl⟩
      simp only [heC, not_false_eq_true, heD, and_self, map_map C D hP, true_and]
      use x, y
    · rintro ⟨⟨heC, heD⟩, x, y, hbtw, rfl, rfl⟩
      simp only [heD, not_false_eq_true, heC, true_and]
      use ⋃₀ (G ↾ C).Component x, ⋃₀ (G ↾ C).Component y, (by use x, y), map_map C D hP, map_map C D hP

lemma setContract_comm (hP : G.IsPartitionGraph) : (G / C) / D = (G / D) / C := by
  rw [SetContract.contract_contract _ _ hP, SetContract.contract_contract _ _ hP, union_comm]


/-- Many different definitions of minor. -/

inductive IspMinor : Graph (Set α) ε → Graph (Set α) ε → Prop
  | refl G : IspMinor G G
  | contract G H (C : Set ε) : IspMinor G H → IspMinor (G / C) H
  | vxDelete G H (S : Set (Set α)) : IspMinor G H → IspMinor (G - S) H
  | edgeDelete G H (D : Set ε) : IspMinor G H → IspMinor (G ＼ D) H

  -- ∃ (S : Set (Set α)) (C D : Set ε), G = (H - S) / C ＼ D

inductive IsrMinor : Graph α ε → Graph α ε → Prop
  | repFun G H (G' : Graph (Set α) ε) (f : Set α → α) :
    G'.IspMinor H.Setify → (∀ s ∈ G'.V, f s ∈ s) → G = G'.vxMap f → IsrMinor G H

def IsiMinor (G : Graph α' ε') (H : Graph α ε) : Prop :=
  ∃ (G' : Graph (Set α) ε), G'.IspMinor (H.Setify) ∧ G ≤↔ G'

def HasCliqueMinor (G : Graph α ε) (n : ℕ) : Prop :=
  (CompleteGraph n).IsiMinor G

variable {α α' : Type u_1} {ε ε' : Type u_2} [Nonempty α] [Nonempty α'] [Nonempty ε] [Nonempty ε']
  {χ : Type*}{G H : Graph α ε} {G' H' : Graph α' ε'}

lemma iff_exists_isom_Setify (P : {α : Type u_1} → {ε : Type u_2} → Graph α ε → Prop)
    [hP : GraphicFunction P] : P G ↔ ∃ (G' : Graph (Set α) ε), P G' ∧ G ≤↔ G' := by
  constructor
  · rintro h
    refine ⟨G.Setify, ?_, Setify.HasIsom G⟩
    rwa [hP.presv_isom G G.Setify (Setify.HasIsom G)] at h
  · rintro ⟨G', h, h'⟩
    rwa [hP.presv_isom _ _ h']

lemma forall_Setify (F : {α : Type u_1} → {ε : Type u_2} → Graph α ε → Prop) [hF : GraphicFunction F]
    (h : ∀ (G' : Graph (Set α) ε), G'.IsPartitionGraph → F G') : ∀ (G : Graph α ε), F G :=
  fun G => by
    rw [hF.presv_isom G G.Setify (Setify.HasIsom G)]
    exact h G.Setify <| Setify.IsPartitionGraph G

instance instIsiMinorleftGraphic : GraphicFunction (fun G ↦ G.IsiMinor H) where
  presv_isom G G' h := by
    unfold IsiMinor
    rw [eq_iff_iff]
    constructor
    · rintro ⟨I, hI, hHI⟩
      exact ⟨I, hI, h.symm.trans hHI⟩
    · rintro ⟨I, hI, hHI⟩
      exact ⟨I, hI, h.trans hHI⟩

instance instIsiMinorrightGraphic : GraphicFunction (fun G ↦ H.IsiMinor G) where
  presv_isom G G' h := by
    unfold IsiMinor
    rw [eq_iff_iff]
    constructor
    · sorry
    · sorry

instance instHasCliqueMinorGraphic {n : ℕ} : GraphicFunction (fun G ↦ G.HasCliqueMinor n) where
  presv_isom G G' h := instIsiMinorrightGraphic.presv_isom G G' h

lemma HasIsom.HasCliqueMinor {α α' ε ε' : Type*} [Nonempty α] [Nonempty α']
    [Nonempty ε] [Nonempty ε'] {G : Graph α ε} {G' : Graph α' ε'} {n : ℕ} (hisom : G ≤↔ G') :
    G.HasCliqueMinor n ↔ G'.HasCliqueMinor n := by
  refine ⟨fun ⟨H, hiMinor, hKn⟩ ↦ ?_, fun ⟨H, hiMinor, hKn⟩ ↦ ?_⟩
  · sorry
  · sorry

end Graph
