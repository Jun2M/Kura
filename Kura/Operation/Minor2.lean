import Kura.Operation.VxIdentification
import Kura.Connected
import Canonical

open Set Function
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

noncomputable def SetContract (G : Graph (Set α) β) (C : Set β) : Graph (Set α) β :=
  G.VxIdentification (G ↾ C).ConnectivityPartition ＼ C

-- scoped infix:70 " / " => Graph.SetContract

noncomputable instance : HDiv (Graph (Set α) β) (Set β) (Graph (Set α) β) where
  hDiv := SetContract

def setContract_def (G : Graph (Set α) β) (C : Set β) : G / C = G.SetContract C := rfl

@[simp]
lemma setContract_vertexSet (G : Graph (Set α) β) (C : Set β) :
  V(G / C) = (⋃₀ (G ↾ C).Component · ) '' V(G) := by
  rw [← connectivityPartition_partOf]
  rfl

instance instvertexSetSetContractFinite (G : Graph (Set α) β) (C : Set β) [Finite V(G)] :
    Finite V(G / C) := by
  rw [setContract_vertexSet]
  infer_instance

@[simp]
lemma SetContract_edgeSet (G : Graph (Set α) β) (C : Set β) : E(G / C) = E(G) \ C :=
  congrArg (· \ C) (VxIdentification_edgeSet G _)

instance instedgeSetSetContractFinite (G : Graph (Set α) β) (C : Set β) [Finite E(G)] :
    Finite E(G / C) := by
  rw [SetContract_edgeSet]
  infer_instance

lemma setContract_edgeSet_ncard_le (G : Graph (Set α) β) (C : Set β) [Finite E(G)] :
    E(G / C).ncard ≤ E(G).ncard := by
  rw [SetContract_edgeSet]
  exact G.edgeDelete_edgeSet_ncard_le C

lemma setContract_edgeSet_ncard_lt_iff (G : Graph (Set α) β) (C : Set β) [Finite E(G)] :
    E(G / C).ncard < E(G).ncard ↔ (E(G) ∩ C).Nonempty := by
  rw [SetContract_edgeSet]
  exact G.edgeDelete_edgeSet_ncard_lt_iff C

lemma setContract_edgeSet_ncard_lt_singleton_iff (G : Graph (Set α) β) (e : β) [Finite E(G)] :
    E(G / ({e} : Set β )).ncard < E(G).ncard ↔ e ∈ E(G) := by
  rw [SetContract_edgeSet]
  exact G.edgeDelete_singleton_edgeSet_ncard_lt_iff e

@[simp]
lemma SetContract_isLink (G : Graph (Set α) β) (C : Set β) (e : β) (x y : Set α) :
    (G / C).IsLink e x y ↔ (e ∉ C ∧ ∃ x', ⋃₀ (G ↾ C).Component x' = x ∧ ∃ y', ⋃₀ (G ↾ C).Component y' = y ∧ G.IsLink e x' y') := by
  rw [← connectivityPartition_partOf, setContract_def, SetContract, edgeDelete_isLink,
    vxIdentification_isLink]

variable {G : Graph (Set α) β} {C D : Set β}

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
  simp_rw [setContract_def, SetContract, ← connectivityPartition_partOf, inc_iff_exists_isLink,
    edgeDelete_isLink, exists_and_left, ← inc_iff_exists_isLink, vxIdentification_inc]

@[simp]
lemma setContract_isLink {u v : Set α} : (G / C).IsLink e u v ↔
    e ∉ C ∧ (∃ x, ⋃₀ (G ↾ C).Component x = u ∧ ∃ y, ⋃₀ (G ↾ C).Component y = v ∧ G.IsLink e x y) := by
  simp_rw [setContract_def, SetContract, ← connectivityPartition_partOf, edgeDelete_isLink,
    vxIdentification_isLink]

lemma SetContract.subset_map (C : Set β) {u : Set α} (hu : u ∈ V(G)) : u ⊆ ⋃₀ (G ↾ C).Component u :=
  subset_sUnion_of_subset ((G ↾ C).Component u) u (fun _ a ↦ a) (VxConnected.refl hu)

lemma SetContract.map_eq_iff' {u v : Set α} (hP : G.IsPartitionGraph) (hv : v ∈ V(G)) :
    ⋃₀ (G ↾ C).Component u = ⋃₀ (G ↾ C).Component v ↔ (G ↾ C).VxConnected u v := by
  obtain ⟨P, hP⟩ := hP
  rw [← hP] at hv
  constructor <;> intro h
  · have : v ⊆ ⋃₀ (G ↾ C).Component v := subset_map C (hP ▸ hv)
    rw [← h, P.subset_sUnion_iff_mem hv (by rw [hP, ← edgeRestrict_vertexSet]; exact component_subset_V)] at this
    simpa using this
  · ext x
    simp only [mem_sUnion, mem_component_iff]
    have : ∀ t, (G ↾ C).VxConnected u t ↔ (G ↾ C).VxConnected v t := fun _ ↦ rel_congr_left h
    simp_rw [this]

lemma SetContract.map_eq_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ V(G)) :
    ⋃₀ (G ↾ C).Component u = ⋃₀ (G ↾ C).Component v ↔ (G ↾ C).VxConnected u v := by
  rw [eq_comm, vxConnected_comm, SetContract.map_eq_iff' hP hu]

@[simp]
lemma SetContract.map_mem_iff {u : Set α} (hP : G.IsPartitionGraph) :
    (⋃₀ (G ↾ C).Component u) ∈ V(G / C) ↔ u ∈ V(G) := by
  simp only [setContract_vertexSet, mem_image]
  constructor <;> rintro h
  · obtain ⟨x, hx, heq⟩ := h
    rw [map_eq_iff hP hx] at heq
    exact heq.mem_right
  · use u

-- @[simp]
-- lemma SetContract.merged_iff {u v : Set α} (hP : G.IsPartitionGraph) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
--     (∃ x ∈ V(G / C), u ⊆ x ∧ v ⊆ x) ↔ (G ↾ C).Connected u v := by
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

lemma SetContract.IsPartitionGraph (C : Set β) (hP : G.IsPartitionGraph) :
    (G / C).IsPartitionGraph := by
  obtain ⟨P, hP⟩ := hP
  use (G ↾ C).ConnectivityPartition.flatten (by use P; simp [hP])
  simp only [Partition.flatten_parts, sSup_eq_sUnion, connectedPartition_parts, ComponentSets,
    edgeRestrict_vertexSet, setContract_vertexSet, connectivityPartition_partOf]
  rw [image_image]

lemma setContract_edgeDel_comm (G : Graph (Set α) β) (hCD : Disjoint C D) :
    G / C ＼ D = (G ＼ D) / C := by
  have heq : (G ↾ C) = (G ＼ D) ↾ C := by
    rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_eq_edgeRestrict_iff]
    tauto_set
  refine ext_inc ?_ fun e x ↦ ?_
  · ext u
    simp only [edgeDelete_vertexSet, setContract_vertexSet, heq, mem_image]
  · simp only [edgeDelete_inc, setContract_inc, ← heq]
    tauto

lemma SetContract.foo {u v : Set α} (hP : G.IsPartitionGraph)
    (hTconn : (G / C ↾ D).VxConnected (⋃₀ (G ↾ C).Component v) (⋃₀ (G ↾ C).Component u)) :
    (G ↾ (C ∪ D)).VxConnected v u := by
  have hu : u ∈ V(G) := (SetContract.map_mem_iff hP).mp hTconn.mem_right
  have hv : v ∈ V(G) := (SetContract.map_mem_iff hP).mp hTconn.mem_left
  obtain ⟨w, hwVd, hwfst, hwlst⟩ := vxConnected_iff_exists_walk.mp hTconn ; clear hTconn
  induction w generalizing v with
  | nil v =>
    simp only [WList.nil_first, WList.nil_last] at hwfst hwlst
    rw [hwfst, map_eq_iff' hP hu] at hwlst
    exact hwlst.of_le (edgeRestrict_mono_right G subset_union_left)
  | cons a e w ih =>
    simp only [WList.first_cons, WList.last_cons, cons_isWalk_iff, edgeRestrict_isLink,
      setContract_isLink] at hwfst hwlst hwVd
    obtain ⟨⟨heD, heC, x, rfl, y, hy, hbtw⟩, hwVd⟩ := hwVd
    rw [map_eq_iff' hP hv] at hwfst
    exact hwfst.symm.of_le (edgeRestrict_mono_right G subset_union_left)
    |>.trans ((edgeRestrict_isLink _ _ _ _ _).mpr ⟨by tauto, hbtw⟩).vxConnected
    |>.trans (ih hbtw.vx_mem_right hwVd hy.symm hwlst)

lemma SetContract.foo2 {u v : Set α} (hP : G.IsPartitionGraph) (h : (G ↾ (C ∪ D)).VxConnected v u) :
    (G / C ↾ D).VxConnected (⋃₀ (G ↾ C).Component v) (⋃₀ (G ↾ C).Component u) := by
  obtain ⟨w, hwVd, rfl, rfl⟩ := vxConnected_iff_exists_walk.mp h ; clear h
  induction w with
  | nil x =>
    simp only [WList.nil_last, WList.nil_first, vxConnected_self, edgeRestrict_vertexSet, vertexSet,
      mem_image]
    use x, by simpa using hwVd
    rw [connectivityPartition_partOf]
  | cons a e w ih =>
    simp only [cons_isWalk_iff, edgeRestrict_isLink, mem_union, WList.last_cons,
      WList.first_cons] at hwVd ⊢
    obtain ⟨⟨he, hbtw⟩, hwVd⟩ := hwVd
    by_cases heC : e ∈ C <;> refine VxConnected.trans ?_ (ih hwVd)
    · convert VxConnected.refl ?_ using 1
      · rw [map_eq_iff' hP hbtw.vx_mem_left]
        exact ((edgeRestrict_isLink _ _ _ _ _).mpr ⟨heC, hbtw.symm⟩).vxConnected
      · use a, hbtw.vx_mem_left
        rw [connectivityPartition_partOf]
    · simp only [heC, false_or] at he
      refine IsLink.vxConnected ?_ (e := e)
      simp only [edgeRestrict_isLink, he, setContract_isLink, heC, not_false_eq_true, true_and]
      use a, rfl, w.first

lemma SetContract.map_map (C D : Set β) (hP : G.IsPartitionGraph) {v : Set α}  :
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

lemma SetContract.contract_contract (C D : Set β) (hP : G.IsPartitionGraph) :
    (G / C) / D = G / (C ∪ D) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · ext u
    simp only [setContract_vertexSet, mem_image, exists_exists_and_eq_and, map_map C D hP]
  · simp only [setContract_isLink, mem_union, not_or]
    constructor
    · rintro ⟨heD, _, rfl, _, rfl, ⟨heC, x, rfl, y, rfl, hbtw⟩⟩
      simp only [heC, not_false_eq_true, heD, and_self, map_map C D hP, true_and]
      use x, rfl, y
    · rintro ⟨⟨heC, heD⟩, x, rfl, y, rfl, hbtw⟩
      simp only [heD, not_false_eq_true, heC, true_and]
      have := map_map C D hP (v := x)
      use ⋃₀ (G ↾ C).Component x, map_map C D hP, ⋃₀ (G ↾ C).Component y, map_map C D hP, x, rfl, y

lemma setContract_comm (hP : G.IsPartitionGraph) : (G / C) / D = (G / D) / C := by
  rw [SetContract.contract_contract _ _ hP, SetContract.contract_contract _ _ hP, union_comm]


/-- Many different definitions of minor. -/

inductive IspMinor : Graph (Set α) β → Graph (Set α) β → Prop
  | refl G : IspMinor G G
  | contract G H (C : Set β) : IspMinor G H → IspMinor (G / C) H
  | vxDelete G H (S : Set (Set α)) : IspMinor G H → IspMinor (G - S) H
  | edgeDelete G H (D : Set β) : IspMinor G H → IspMinor (G ＼ D) H

  -- ∃ (S : Set (Set α)) (C D : Set β), G = (H - S) / C ＼ D

inductive IsrMinor : Graph α β → Graph α β → Prop
  | repFun G H (G' : Graph (Set α) β) (f : Set α → α) :
    G'.IspMinor H.Setify → (∀ s ∈ V(G'), f s ∈ s) → G = G'.vxMap f → IsrMinor G H

def IsiMinor (G : Graph α' β') (H : Graph α β) : Prop :=
  ∃ (G' : Graph (Set α) β), G'.IspMinor (H.Setify) ∧ G ↔ᴳ G'

def HasCliqueMinor (G : Graph α β) (n : ℕ) : Prop :=
  (CompleteGraph n).IsiMinor G

variable {α α' β β' χ : Type*} {G H : Graph α β} {G' H' : Graph α' β'}

lemma iff_exists_isom_setify (P : {α : Type u_6} → {β : Type u_8} → Graph α β → Prop)
    [hP : GraphicFunction P P] : P G ↔ ∃ (G' : Graph (Set α) β), P G' ∧ G ↔ᴳ G' := by
  constructor
  · rintro h
    refine ⟨G.Setify, ?_, setify_hasIsom G⟩
    rwa [hP.invariant (setify_hasIsom G)] at h
  · rintro ⟨G', h, h'⟩
    rwa [hP.invariant h']

instance instIsiMinorleftGraphic : GraphicFunction (·.IsiMinor H) (·.IsiMinor H) where
  invariant h := by
    unfold IsiMinor
    rw [eq_iff_iff]
    constructor
    · rintro ⟨I, hI, hHI⟩
      exact ⟨I, hI, h.symm.trans hHI⟩
    · rintro ⟨I, hI, hHI⟩
      exact ⟨I, hI, h.trans hHI⟩

instance instIsiMinorrightGraphic : GraphicFunction H.IsiMinor H.IsiMinor where
  invariant h := by
    unfold IsiMinor
    rw [eq_iff_iff]
    constructor
    · sorry
    · sorry

instance instHasCliqueMinorGraphic {n : ℕ} :
    GraphicFunction (·.HasCliqueMinor n) (·.HasCliqueMinor n) :=
  instIsiMinorrightGraphic

instance instHasCliqueMinorGraphicVertex {n : ℕ} :
    GraphicVertexFunction (fun (G : Graph α _) ↦ G.HasCliqueMinor n) (fun (G : Graph α _) ↦ G.HasCliqueMinor n) :=
  instGraphicGraphicVertex (hF := instHasCliqueMinorGraphic)

lemma vxConnected_in_edgeRestrict_singleton_inc {G : Graph (Set α) β} {e : β} {v z : Set α}
    (hv_is_endpoint : G.Inc e v) (h_conn_vz : (G ↾ {e}).VxConnected v z) : G.Inc e z := by
  let G' := G ↾ {e}
  rw [vxConnected_edgeRestrict_singleton] at h_conn_vz
  obtain ⟨rfl, hv⟩ | h_link_e_v_z := h_conn_vz.symm
  · exact hv_is_endpoint

  obtain ⟨x, y, he_link_xy⟩ := G.exists_isLink_of_mem_edgeSet hv_is_endpoint.edge_mem
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he_link_xy.eq_and_eq_or_eq_and_eq_of_isLink h_link_e_v_z
  · exact he_link_xy.inc_right
  · exact he_link_xy.inc_left

lemma vxConnected_in_edgeRestrict_isolated {G : Graph (Set α) β} {F: Set β} {v z : Set α}
    (h_ninc : ∀ e ∈ F, ¬ G.Inc e v) (h_conn_vz : (G ↾ F).VxConnected v z) : z = v := by
  obtain ⟨P, hP, rfl, rfl, hPF⟩ := vxConnected_edgeRestrict.mp h_conn_vz
  by_cases hPnil : P.Nil
  · exact (WList.Nil.first_eq_last hPnil).symm

  exfalso
  obtain ⟨a, e, P'⟩ := WList.not_nil_iff.mp hPnil
  simp_all only [cons_isPath_iff, WList.first_cons, WList.cons_edgeSet, WList.last_cons,
    WList.not_nil_cons, not_false_eq_true]
  obtain ⟨hP', heaP', haP'⟩ := hP
  exact h_ninc e (hPF <| mem_insert e P'.edgeSet) heaP'.inc_left

lemma map_vertex_singleton_contract (G : Graph (Set α) β) {e : β} {x y : Set α} (he : G.IsLink e x y)
    [DecidableRel G.Inc] {v : Set α} (hv : v ∈ V(G)) : (⋃₀ (G ↾ {e}).Component v) = if G.Inc e v then x ∪ y else v := by
  let G' := G ↾ {e}

  have v_mem_G' : v ∈ V(G') := edgeRestrict_vertexSet G {e} ▸ hv
  have hx_mem_G' : x ∈ V(G') := edgeRestrict_vertexSet G {e} ▸ he.vx_mem_left
  have hy_mem_G' : y ∈ V(G') := edgeRestrict_vertexSet G {e} ▸ he.vx_mem_right

  split_ifs with h_inc_e_v
  · -- Case: G.Inc e v is true (h_inc_e_v : G.Inc e v)
    have h_comp_eq_xy : G'.Component v = {x, y} := by
      ext z_ext
      simp only [mem_component_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Goal: G'.VxConnected v z_ext → z_ext = x ∨ z_ext = y
        intro h_conn_v_z_ext
        have h_inc_e_z_ext : G.Inc e z_ext :=
          vxConnected_in_edgeRestrict_singleton_inc h_inc_e_v h_conn_v_z_ext
        -- From G.Inc e z_ext and he : G.IsLink e x y, we deduce z_ext = x ∨ z_ext = y.
        exact h_inc_e_z_ext.eq_or_eq_of_isLink he
      · -- Goal: z_ext = x ∨ z_ext = y → G'.VxConnected v z_ext
        rintro (rfl | rfl) <;> obtain (rfl | rfl) : v = _ ∨ v = _ := h_inc_e_v.eq_or_eq_of_isLink he
        · exact VxConnected.refl hx_mem_G'
        · exact (G.edgeRestrict_isLink {e} e _ _).mpr ⟨Set.mem_singleton e, he.symm⟩ |>.vxConnected
        · exact (G.edgeRestrict_isLink {e} e _ _).mpr ⟨Set.mem_singleton e, he⟩ |>.vxConnected
        · exact VxConnected.refl hy_mem_G'
    rw [h_comp_eq_xy, sUnion_insert, sUnion_singleton]

  · -- Case: G.Inc e v is false (h_inc_e_v : ¬ G.Inc e v)
    have h_comp_eq_v : G'.Component v = {v} := by
      ext z_ext
      simp only [mem_component_iff, Set.mem_singleton_iff]
      constructor
      · -- Goal: G'.VxConnected v z_ext → z_ext = v
        exact vxConnected_in_edgeRestrict_isolated (fun e_s he_s_mem_eq => by
          rwa [mem_singleton_iff.mp he_s_mem_eq])
      · -- Goal: z_ext = v → G'.VxConnected v z_ext
        rintro rfl
        exact VxConnected.refl v_mem_G'
    rw [h_comp_eq_v, sUnion_singleton]

end Graph
