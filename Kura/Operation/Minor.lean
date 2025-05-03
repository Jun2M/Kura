import Kura.Connected
import Kura.Operation.Map


open Set Function
variable {α α' α'' β β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

/-- `Contract G φ C` contracts the edges in set `C` of graph `G`,
    mapping the resulting vertices according to function `φ`.

    This operation creates a new graph where:
    1. Edges in set `C` are removed
    2. Vertices are relabeled according to the mapping function `φ`

    This is the fundamental operation for creating graph minors. -/
def Contract (G : Graph α β) (φ : α → α') (C : Set β) : Graph α' β :=
  (G.vxMap φ) ↾ (G.E \ C)

notation:70 G " /["φ"] " C => Graph.Contract G φ C

/- lemmas about Contract -/

variable {φ τ : α → α'} {C D : Set β}

@[simp]
lemma contract_vxSet : (G /[φ] C).V = φ '' G.V := rfl

@[simp]
lemma contract_edgeSet : (G /[φ] C).E = G.E \ C := by
  simp only [Contract, vxMap, edgeRestrict_edgeSet, oftoMultiset_edgeSet, Multiset.card_map,
    toMultiset_card_eq_two_iff, setOf_mem_eq, inter_eq_right]
  tauto_set

lemma contract_edgeSet_subset : (G /[φ] C).E ⊆ G.E := by
  simp only [contract_edgeSet]
  tauto_set

@[simp]
lemma contract_inc : (G /[φ] C).Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [Contract, edgeRestrict_inc, mem_diff, vxMap_inc, iff_def,
    not_false_eq_true, and_self, implies_true, and_true, and_imp, forall_exists_index, true_and]
  exact fun heC x hinc rfl ↦ hinc.edge_mem

lemma inc₂_of_inc₂ (hbtw : G.Inc₂ e u v) (hnin : e ∉ C) : (G /[φ] C).Inc₂ e (φ u) (φ v) := by
  simp only [Contract, edgeRestrict_inc₂, mem_diff, hbtw.edge_mem, hnin, not_false_eq_true,
    and_self, vxMap_inc₂', true_and]
  use u, v

@[simp]
lemma contract_inc₂ : (G /[φ] C).Inc₂ e x y ↔ e ∉ C ∧ ∃ u v, G.Inc₂ e u v ∧ φ u = x ∧ φ v = y := by
  simp +contextual only [Contract, edgeRestrict_inc₂, mem_diff, vxMap_inc₂', iff_def,
    not_false_eq_true, and_self, implies_true, and_true, and_imp, forall_exists_index, true_and]
  exact fun heC x y hbtw rfl rfl ↦ hbtw.edge_mem

lemma Inc₂.contract (φ : α → α') (he : e ∉ C) (hbtw : G.Inc₂ e u v) :
    (G /[φ] C).Inc₂ e (φ u) (φ v) := by
  rw [Contract, edgeRestrict_inc₂, vxMap_inc₂']
  use ⟨hbtw.edge_mem, he⟩, u, v

namespace Contract

/-- A function `φ` is valid on a graph `G` with respect to a set of edges `C` if
    it maps two vertices to the same vertex precisely when they are connected
    in the subgraph induced by the edges in `C`.

    This property ensures that contraction preserves the structure of the graph
    in a well-defined way. -/
def ValidIn (G : Graph α β) (φ : α → α') (C : Set β) :=
  ∀ ⦃x y⦄, x ∈ G.V → y ∈ G.V → (φ x = φ y ↔ (G ↾ C).VxConnected x y)

@[simp]
lemma map_mem (φ : α → α') (C : Set β) (hx : u ∈ G.V) : φ u ∈ (G /[φ] C).V := by
  use u

-- lemma map_eq_of_reflAdj (hC : ValidIn G φ C) (hradj : (G ↾ C).reflAdj u v) : φ u = φ v := by
--   obtain h | ⟨rfl, h⟩ := hradj
--   · rw [hC h.mem_left h.mem_right]
--     exact h.connected
--   · rfl

lemma ValidIn.of_inter_eq (hC : ValidIn G φ C) (h : C ∩ G.E = D ∩ G.E) :
    ValidIn G φ D := by
  rwa [ValidIn, ← (G.edgeRestrict_eq_edgeRestrict_iff C D).mpr h]

lemma toFun_eq_of_inter_eq_fixed_eq (hC : ValidIn G φ C) (hD : ValidIn G τ C)
    (hfixed : ∀ a ∈ G.V, ∃ x ∈ G.V, τ x = φ a ∧ φ x = φ a) : EqOn φ τ G.V := by
  rintro x hx
  obtain ⟨y, hy, htypx, hpypx⟩ := hfixed x hx
  rwa [← htypx, hD hy hx, ← hC hy hx]

lemma toFun_eq_of_inter_eq_fixed_eq' (hC : ValidIn G φ C) (hD : ValidIn G τ D)
    (hinter : C ∩ G.E = D ∩ G.E)
    (hfixed : ∀ a ∈ G.V, ∃ x ∈ G.V, τ x = φ a ∧ φ x = φ a) : EqOn φ τ G.V := by
  rintro x hx
  obtain ⟨y, hy, hτyφx, hφyφx⟩ := hfixed x hx
  rwa [← hτyφx, hD hy hx, ← (G.edgeRestrict_eq_edgeRestrict_iff C D).mpr hinter, ← hC hy hx]

-- lemma ValidIn.le (hC : ValidIn G φ C) (hle : H ≤ G) (hE : G.E ∩ C ⊆ H.E) :
--     ValidIn H φ C := by
--   intro x y hx hy
--   rw [hC (vxSet_subset_of_le hle hx) (vxSet_subset_of_le hle hy)]
--   exact ( hle hE hx).symm

-- restrict_Connected_iff_restrict_Connected_of_le
/-- Given a set of edges `S` in a graph, this lemma shows that there exists a valid
    contraction function and corresponding contracted edge set that precisely equals `S`.

    This is useful for showing that any set of edges can be validly contracted. -/
lemma exists_rep_of_contractSet (S : Set β) : ∃ (φ : α → α), ValidIn G φ S := by
  classical
  -- Get a representative function for the connected components
  obtain ⟨φ, hid, hrel, heq⟩ := Partition.nonempty_repFun (ConnectedPartition (G ↾ S))
  use φ
  simp only [connectedPartition_supp, edgeRestrict_vxSet, ConnectedPartition.Rel] at hrel heq
  -- Show that φ is a valid contraction function with respect to S
  intro x y hx hy
  refine ⟨fun h_eq_φ ↦ ?_, (heq _ _ ·)⟩
  obtain hconny := hrel y hy
  refine ((hrel x hx).trans ?_).trans hconny.symm
  rw [h_eq_φ]
  exact VxConnected.refl hconny.mem_right





/- Assuming m is valid on some G, m represents a set of the subgraphs to be contracted and
  for each subgraph, which vertex label to retain.
  This function restricts the set of subgraphs to only those that retains a vertex labels in R. -/
-- noncomputable def ContractSys.confine {m : ContractSys α β α'} (hmvalid : m.validIn G) (R : Set α) :
--     ContractSys α β α' where
--   toFun v := ite (m v ∈ R) (h := Classical.dec _) (m v) v
--   contractSet := {e ∈ m.contractSet | ∃ v, G.Inc e v ∧ m v ∈ R}

-- lemma ContractSys.ValidIn.confine {m : ContractSys α β} (hmvalid : m.validIn G) (R : Set α) :
--     (m.confine hmvalid R).validIn (G[m.toFun ⁻¹' R]) := by
--   constructor
--   · intro v hv
--     simp only [induce_V, mem_inter_iff, mem_preimage, not_and, ContractSys.confine, ite_eq_right_iff] at hv ⊢
--     rintro hinR
--     have : v ∉ G.V := fun a ↦ hv a hinR
--     exact hmvalid.map_not_mem_simp this
--   · simp only [induce_V, mem_inter_iff, mem_preimage, ContractSys.confine, induce_restrict_eq_subgraph,
--     and_imp]
--     rintro v hv hinR
--     simp only [hinR, ↓reduceIte]
--     have : G{{e | e ∈ m.contractSet ∧ ∃ v, G.Inc v e ∧ m.toFun v ∈ R}}[m.toFun ⁻¹' R] =
--       G{m.contractSet}[m.toFun ⁻¹' R] := by
--       ext x e
--       · simp only [induce_V, restrict_V, mem_inter_iff, mem_preimage]
--       · simp only [induce_E, restrict_E, restrict_inc, mem_setOf_eq, mem_preimage, and_imp,
--         forall_exists_index, mem_inter_iff]
--         constructor
--         · rintro ⟨⟨he, hin, v, hinc, hvR⟩, hR⟩
--           tauto
--         · rintro ⟨⟨he, hin⟩, h⟩
--           refine ⟨⟨he, hin, ?_⟩, ?_⟩
--           · obtain ⟨u, huin⟩ := G.exists_vertex_inc he
--             use u, huin, h u huin hin
--           · rintro a hainc _ b hbinc hbR
--             exact h a hainc hin
--       · simp only [induce_inc, restrict_inc, mem_setOf_eq, mem_preimage, and_imp,
--         forall_exists_index]
--         tauto
--     rw [this]; clear this
--     apply (hmvalid.map_connected hv).induce_of_mem
--     rintro x hxconn
--     simp only [mem_preimage]
--     rwa [← hmvalid.map_eq_of_connected hxconn]
--   · simp only [ContractSys.confine, mem_setOf_eq, induce_inc, mem_preimage, and_imp, forall_exists_index]
--     rintro x y e hem z hzinc hzR hxinc hinR hyinc hinR'
--     clear hzR hzinc z hinR'
--     simp only [hinR _ hxinc, ↓reduceIte, hinR _ hyinc]
--     exact hmvalid.map_edge hem hxinc hyinc


@[simp]
lemma contract_eq_contract_iff : (G /[φ] C) = (G /[φ] D) ↔ G.E \ C = G.E \ D := by
  constructor <;> rintro hE
  · apply_fun Graph.E at hE
    simpa using hE
  · have hE' := Set.ext_iff.mp hE
    simp only [mem_diff, and_congr_right_iff] at hE'
    refine ext_inc (by simp) fun e x ↦ ?_
    simp only [contract_inc, and_congr_left_iff, forall_exists_index, and_imp]
    exact fun a hinc rfl ↦ hE' e hinc.edge_mem

@[simp]
lemma contract_restrict_eq_restrict_contract {S : Set β} :
    (G /[φ] C) ↾ S = ((G ↾ (S ∪ (G.E ∩ C))) /[φ] C) := by
  refine ext_inc (by simp) fun e x ↦ ?_
  simp only [edgeRestrict_inc, contract_inc, mem_union, mem_inter_iff]
  tauto

@[simp]
lemma contract_vxDel_eq_vxDel_contract {S : Set α'} : (G /[φ] C) - S = (G - (φ ⁻¹' S)) /[φ] C := by
  apply Graph.ext
  · ext v
    simp only [vxDelete_vxSet, contract_vxSet, mem_diff, mem_image, mem_preimage]
    simp_rw [← exists_and_right, and_assoc, and_comm]
    refine exists_congr (fun x ↦ ?_)
    simp_all only [and_congr_right_iff, implies_true]
  · rintro e x y
    simp only [iff_def, vxDelete_inc₂, contract_inc₂, contract_vxSet, mem_image, mem_preimage]
    constructor
    · rintro ⟨⟨heC, u, v, huv, rfl, rfl⟩, ⟨-, hu⟩, ⟨-, hv⟩⟩
      use heC, u, v, ?_
      use huv, ⟨huv.vx_mem_left, hu⟩, huv.vx_mem_right, hv
    · rintro ⟨heC, u, v, ⟨huv, ⟨hu, huS⟩, hv, hvS⟩, rfl, rfl⟩
      tauto

end Contract

/- Creators of ContractSys -/

/-- Creates a contraction system from a single edge incident to a vertex.

    Given a vertex `u` incident to edge `e`, this creates a contraction system
    that contracts edge `e` and maps all vertices incident to `e` to `u`. -/
def Inc.contractFun (_hxe : G.Inc e u) [DecidablePred (G.Inc e)] : α → α :=
  fun v ↦ if G.Inc e v then u else v

lemma Inc.contractFun_validIn (hxe : G.Inc e u) [DecidablePred (G.Inc e)] :
    Contract.ValidIn G (Inc.contractFun hxe) {e} := by
  rintro a b ha hb
  simp only [contractFun]
  split_ifs with hainc hbinc hbinc
  · simp only [true_iff]
    by_cases hab : a = b
    · subst b
      exact VxConnected.refl ha
    · refine Inc₂.vxConnected ?_ (e := e)
      rw [edgeRestrict_inc₂]
      exact ⟨rfl, hainc.inc₂_of_inc_of_ne hbinc hab⟩
  · apply iff_of_false
    · rintro rfl
      exact hbinc hxe
    · have hab : a ≠ b := by
        rintro rfl
        exact hbinc hainc
      rw [vxConnected_comm, Isolated.connected_iff ?_]
      tauto
      · rintro e' he'
        simp only [edgeRestrict_inc, mem_singleton_iff] at he'
        obtain ⟨rfl, he⟩ := he'
        exact hbinc he
  · apply iff_of_false
    · rintro rfl
      exact hainc hxe
    · have hab : a ≠ b := by
        rintro rfl
        exact hainc hbinc
      rw [Isolated.connected_iff ?_]
      tauto
      · rintro e' he'
        simp only [edgeRestrict_inc, mem_singleton_iff] at he'
        obtain ⟨rfl, he⟩ := he'
        exact hainc he
  · rw [Isolated.connected_iff ?_]
    simp [ha]
    · rintro e' he'
      simp only [edgeRestrict_inc, mem_singleton_iff] at he'
      obtain ⟨rfl, he⟩ := he'
      exact hainc he

def Inc₂.contractFun (_hexy : G.Inc₂ e u v) [DecidableEq α] : α → α :=
  fun w ↦ if w = v then u else w

lemma Inc₂.contractFun_validIn (hexy : G.Inc₂ e u v) [DecidableEq α] :
    Contract.ValidIn G hexy.contractFun {e} := by
  rintro a b ha hb
  have hsub := (G.edgeRestrict_edgeSet {e}) ▸ inter_subset_left
  simp only [contractFun]
  split_ifs with hainc hbinc hbinc
  · subst hainc hbinc
    simp only [true_iff]
    exact VxConnected.refl hb
  · subst hainc
    rw [← ne_eq, ne_comm] at hbinc
    simp [vxConnected_edgeRestrict_singleton, hbinc, hexy.symm.inc₂_iff_eq_right]
  · subst hbinc
    simp [vxConnected_edgeRestrict_singleton, hainc, hexy.inc₂_iff_eq_left, eq_comm]
  · rw [vxConnected_edgeRestrict_singleton]
    have hnadj : ¬ G.Inc₂ e a b := by
      rintro hbtw
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hexy.eq_and_eq_or_eq_and_eq_of_inc₂ hbtw
      · exact hbinc rfl
      · exact hainc rfl
    simp [hnadj, ha]

lemma Inc₂.contractFun_eq_self_of_not_inc [DecidableEq α] (hexy : G.Inc₂ e u v)
    (h : ¬ G.Inc e u) : hexy.contractFun u = u := by
  simp only [contractFun, ite_eq_right_iff]
  rintro rfl
  exact (h hexy.inc_right).elim

@[simp]
lemma Inc₂.contractFun_eq_self_iff [DecidableEq α] (hexy : G.Inc₂ e u v) (huv : u ≠ v) :
    hexy.contractFun u = u ↔ u ≠ v := by
  simp +contextual [Inc₂.contractFun, huv]

@[simp]
lemma Inc₂.vx_mem_contract_iff [DecidableEq α] (hexy : G.Inc₂ e u v) :
    w ∈ (G /[hexy.contractFun] {e}).V ↔ w ∈ G.V \ {v} ∪ {u} := by
  simp +contextual only [contract_vxSet, Inc₂.contractFun, mem_image, union_singleton,
    mem_insert_iff, mem_diff, mem_singleton_iff, iff_def, forall_exists_index, and_imp]
  constructor
  · rintro w hw rfl
    split_ifs with h <;> simp [h, hw]
  · rintro (rfl | ⟨h, hnin⟩)
    · use v, hexy.vx_mem_right, (by simp)
    . use w, h, (by simp [hnin])

open Contract
variable {φ : α → α'} {τ : α' → α''} {C D : Set β} {x y : α'}

-- instance instFinite [h : G.Finite] : (G /[φ] C).Finite where
--   vx_fin := Set.Finite.image φ h.vx_fin
--   edge_fin := by
--     apply Set.Finite.subset (h.edge_fin)
--     exact E_subset

lemma reflAdj (hbtw : G.reflAdj u v) (hVd : ValidIn G φ C) : (G /[φ] C).reflAdj (φ u) (φ v) := by
  obtain ⟨e', hbtw'⟩ | ⟨rfl, huv⟩ := hbtw
  · by_cases he : e' ∈ C
    · have : G{C}.Connected u v := by
        apply Inc₂.connected
        rw [restrict_inc₂_iff]
        exact ⟨hbtw', he⟩
      rw [← hVd hbtw'.vx_mem_left hbtw'.vx_mem_right] at this
      rw [this]; clear this
      refine reflAdj.of_vxMem ?_
      use v, hbtw'.vx_mem_right
    · exact (inc₂ φ he hbtw').reflAdj
  · exact reflAdj.of_vxMem (by use u)

lemma connected_of_map_reflAdj (hVd : ValidIn G φ C) (hradj : (G /[φ] C).reflAdj (φ u) (φ v))
    (hu : u ∈ G.V) (hv : v ∈ G.V) : G.VxConnected u v := by
  have hle := G.edgeRestrict_le (E₀ := C)
  obtain ⟨e, hbtw⟩ | ⟨heq, hmem⟩ := hradj
  · obtain he := hbtw.edge_mem
    simp only [E, mem_diff] at he
    obtain ⟨he, heC⟩ := he
    obtain ⟨a, b, hbtwG⟩ := Inc₂.exists_vx_inc₂ he
    have heqeq := (inc₂ φ heC hbtwG).eq_or_eq_of_inc₂ hbtw
    wlog heq : φ a = φ u ∧ φ b = φ v
    · simp only [heq, false_or] at heqeq
      rw [and_comm] at heqeq
      apply this hVd hu hv hle e hbtw he heC b a hbtwG.symm ?_ heqeq
      left
      exact heqeq
    rw [hVd hbtwG.vx_mem_left hu, hVd hbtwG.vx_mem_right hv] at heq
    exact ((heq.1.symm.of_le hle).trans (hbtwG.connected)).trans (heq.2.of_le hle)
  · rw [hVd hu hv] at heq
    exact heq.of_le hle

lemma connnected_of_map_connected (hVd : ValidIn G φ C) (hconn : (G /[φ] C).Connected x y) :
    ∀ u ∈ G.V, ∀ v ∈ G.V, φ u = x → φ v = y → G.Connected u v := by
  induction hconn with
  | single hradj =>
    rename_i z
    rintro u hu v hv rfl rfl
    exact connected_of_map_reflAdj hVd hradj hu hv
  | tail hconn hradj ih =>
    obtain ⟨w, hw, rfl⟩ := hradj.mem_left
    rintro u hu v hv rfl rfl
    refine (ih u hu w hw rfl rfl).trans ?_
    exact connected_of_map_reflAdj hVd hradj hw hv

lemma connected (hVd : ValidIn G φ C) (hconn : G.Connected u v) :
    (G /[φ] C).Connected (φ u) (φ v) := by
  induction hconn with
  | single hradj =>
    exact (reflAdj hradj hVd).connected
  | tail hconn hradj ih =>
    exact ih.trans (reflAdj hradj hVd).connected

-- @[simp]
-- lemma connected_iff (hVd : ValidIn G φ C) (hu : u ∈ G.V) (hv : v ∈ G.V) :
--     (G /[φ] C).Connected (φ u) (φ v) ↔ G.Connected u v :=
--   ⟨(connnected_of_map_connected hVd · u hu v hv rfl rfl), connected hVd⟩

-- private lemma connected_restrict_of_reflAdj_restrict_contract (S : Set β) (hVd : ValidIn G φ C)
--     (hu : u ∈ G.V) (hv : v ∈ G.V) (hradj : (G /[φ] C){S}.reflAdj (φ u) (φ v)) :
--     G{C ∪ S}.Connected u v := by
--   rw [reflAdj_iff_or] at hradj
--   obtain ⟨hne, e, hinc, h⟩ | ⟨heq, hin⟩ := hradj
--   · rw [Inc₂] at hinc
--     obtain ⟨u', hequ, v', heqv, hbtw', hnin⟩ := hinc
--     rw [hVd hbtw'.vx_mem_left hu] at hequ
--     rw [hVd hbtw'.vx_mem_right hv] at heqv
--     exact hequ.symm.of_le (G.restrict_mono subset_union_left)
--       |>.trans (hbtw'.restrict_of_mem (mem_union_right C h) |>.connected)
--       |>.trans <| heqv.of_le (G.restrict_mono subset_union_left)
--   · rw [hVd hu hv] at heq
--     exact heq.of_le (G.restrict_mono subset_union_left)

-- private lemma Connected.restrict_of_connected_restrict_contract' (S : Set β) (hVd : ValidIn G φ C)
--     (hu : u ∈ G.V) (hv : v ∈ G.V) (hx : x = φ u) (hy : y = φ v) (h : (G /[φ] C){S}.Connected x y) :
--     G{C ∪ S}.Connected u v := by
--   induction h generalizing v with
--   | single hradj =>
--     subst hx hy
--     exact connected_restrict_of_reflAdj_restrict_contract S hVd hu hv hradj
--   | tail hconn hadj ih =>
--     subst hx hy
--     obtain ⟨w, hw, rfl⟩ := hadj.mem_left
--     exact (ih hw rfl).trans (connected_restrict_of_reflAdj_restrict_contract S hVd hw hv hadj)

-- lemma Connected.restrict_of_connected_restrict_contract (S : Set β) (hVd : ValidIn G φ C)
--     (hu : u ∈ G.V) (hv : v ∈ G.V) (h : (G /[φ] C){S}.Connected (φ u) (φ v)) :
--     G{C ∪ S}.Connected u v :=
--   Connected.restrict_of_connected_restrict_contract' S hVd hu hv rfl rfl h

-- lemma Connected.of_contract (hVd : ValidIn G φ C) (hu : u ∈ G.V) (hv : v ∈ G.V)
--     (h : (G /[φ] C).Connected (φ u) (φ v)) : G.Connected u v := by
--   have := Connected.restrict_of_connected_restrict_contract univ hVd hu hv (by
--     rwa [restrict_univ_eq_self])
--   rwa [union_univ, restrict_univ_eq_self] at this


-- @[simp]
-- theorem Connected.map_restrict_iff_connected_restrict_contract {m : ContractSys α β}
--     (hvalid : m.validIn G) (S : Set β) :
--     (G.contract m hvalid){S}.Connected (m x) (m y) ↔ G{m.contractSet ∪ S}.Connected x y := by
--   constructor
--   · exact Connected.map_restrict_of_connected_restrict_contract hvalid S (x := x) (y := y)
--   · rintro hconn
--     induction hconn with
--     | single hadj => exact connected_contract_restrict_of_restrict_adj hvalid S hadj
--     | tail hconn hadj ih => exact ih.trans <| connected_contract_restrict_of_restrict_adj hvalid S hadj

-- lemma contract_contract_compable {m : ContractSys α β} (hm : m.validIn G)
--   {n : ContractSys α β} (hn : n.validIn (G/m ~hm)) :
--   ∀ (v : α), m (n (m v)) = n (m v) := by
--   rintro v
--   by_cases h : v ∈ G.V
--   · obtain ⟨w, hw, heq⟩ := hn.map_mem (x := m v) (mem_image_of_mem m h)
--     rw [← heq, m.idem]
--   · rw [hn.map_not_mem, m.idem]
--     simp only [contract, mem_image, not_exists, not_and]
--     rw [hm.map_not_mem h]
--     rintro x hx rfl
--     exact h <| hm.map_mem hx

-- lemma contract_contract_comp_validIn {m : ContractSys α β} (hm : m.validIn G)
--     {n : ContractSys α β} (hn : n.validIn (G/m ~hm)) :
--     (n.comp m (contract_contract_compable hm hn)).validIn G := by
--   refine ⟨?_, ?_, ?_⟩
--   · rintro x hx
--     simp only [ContractSys.comp]
--     rw [hm.map_not_mem hx, hn.map_not_mem]
--     exact not_mem_contract_of_not_vx_mem hm hx
--   · rintro x hxmem
--     simp only [ContractSys.comp]
--     have hle := (G.restrict_mono m.contractSet (n.contractSet ∪ m.contractSet) subset_union_right)
--     refine ((hm.map_connected hxmem).le hle).trans
--       (?_ : G{n.contractSet ∪ m.contractSet}.Connected (m.toFun x) (n.toFun (m.toFun x)))
--     rw [union_comm]
--     apply Connected.restrict_of_connected_restrict_contract hm
--     refine hn.map_connected (?_ : m x ∈ _)
--     rwa [map_mem_contract_iff_vx_mem]
--   · rintro x y e he hxinc hyinc
--     simp only [ContractSys.comp] at he ⊢
--     rw [union_comm, ← union_diff_self, mem_union] at he
--     obtain he | he := he
--     · congr 1
--       exact hm.map_edge (e := e) he hxinc hyinc
--     · apply hn.map_edge (e := e) (mem_of_mem_diff he) <;> simp only [contract]
--       · use x, rfl, hxinc
--         exact not_mem_of_mem_diff he
--       · use y, rfl, hyinc
--         exact not_mem_of_mem_diff he

-- @[simp]
-- lemma contract_contract_eq_contract_comp {m : ContractSys α β} (hm : m.validIn G)
--   {n : ContractSys α β} (hn : n.validIn (G/m ~hm)) :
--   ((G/m ~hm)/n ~hn) = G/(n.comp m (contract_contract_compable hm hn))
--     ~(contract_contract_comp_validIn hm hn) := by
--   ext x e <;> simp [contract_V, mem_image, exists_exists_and_eq_and, ContractSys.comp, contract_E,
--     mem_diff, mem_union, not_or]
--   · rw [and_assoc, @and_comm (x ∉ m.contractSet) (x ∉ n.contractSet)]
--   · constructor
--     · rintro ⟨v, rfl, ⟨w, rfl, hinc, henin32⟩, henin21⟩
--       use w
--     · rintro ⟨v, rfl, hinc, henin21, henin32⟩
--       use m v, rfl, ?_
--       use v

-- lemma comp_validIn (hn : ValidIn G φ C) (hm : ValidIn (G /[φ] C) τ D) :
--     ValidIn G (τ ∘ φ) (C ∪ D) := by
--   rintro x y hx hy
--   rw [comp, comp, hm (map_mem _ _ hx) (map_mem _ _ hy)]
--   constructor
--   · rintro hconn


--     use z
--     tauto
--   · rintro ⟨z, rfl, hz⟩
--     use z
--     tauto

-- def Contract.toSubgraph {m : ContractSys α β} (hm : m.validIn G) (v : α) :
--     Graph α β := G{m.contractSet}[m ⁻¹' {v}]

def IsContraction (H G : Graph α β) := ∃ φ C, H = G /[φ] C

-- lemma IsContraction_refl : G.IsContraction G := by
--   refine ⟨ContractSys.id, ⟨?_, ?_, ?_⟩, ?_⟩
--   · simp only [ContractSys.id, id_eq, implies_true]
--   · simp only [ContractSys.id, id_eq]
--     intro x hx
--     apply Connected.refl
--     exact hx
--   · simp only [ContractSys.id, mem_empty_iff_false, id_eq, IsEmpty.forall_iff, implies_true]
--   · simp only [contract, ContractSys.id, id_eq, image_id', diff_empty, mem_empty_iff_false,
--     not_false_eq_true, and_true, exists_eq_left]

-- lemma isContraction_trans {G₁ G₂ G₃ : Graph α β} (hm : G₁.IsContraction G₂)
--     (hm' : G₂.IsContraction G₃) : G₁.IsContraction G₃ := by
--   obtain ⟨m21, hm21, rfl⟩ := hm
--   obtain ⟨m32, hm32, rfl⟩ := hm'
--   use m21.comp m32 (contract_contract_compable hm32 hm21), contract_contract_comp_validIn hm32 hm21
--   exact contract_contract_eq_contract_comp hm32 hm21


-- def IsMinor (G H : Graph α β) := ∃ m, G ≤ H/m

-- notation G " ≤ₘ " H => IsMinor G H

-- lemma IsMinor.refl : G ≤ₘ G := by
--   refine ⟨G.E, G.V, ContractSys.id, ⟨?_, ?_, ?_⟩, ?_⟩
--   · simp only [restrict_E_eq_self, induce_V_eq_self, ContractSys.id, id_eq, implies_true]
--   · simp only [restrict_E_eq_self, induce_V_eq_self, ContractSys.id, id_eq]
--     intro x hx
--     apply Connected.refl
--     exact hx
--   · simp only [ContractSys.id, mem_empty_iff_false, restrict_E_eq_self, induce_V_eq_self, id_eq,
--     IsEmpty.forall_iff, implies_true]
--   · simp only [restrict_E_eq_self, induce_V_eq_self, contract_id_eq_self]

-- lemma IsMinor.trans {G H K : Graph α β} (hGH : G ≤ₘ H) (hHK : H ≤ₘ K) : G ≤ₘ K := by
--   obtain ⟨R, U, m, hm, rfl⟩ := hGH
--   obtain ⟨S, T, n, hn, rfl⟩ := hHK
--   simp only [contract_restrict_eq_restrict_contract, induce_E, restrict_E, restrict_inc, and_imp,
--     induce_restrict_eq_subgraph, restrict_restrict_eq_restrict_inter,
--     contract_induce_eq_induce_contract, induce_induce_eq_induce_inter,
--     contract_contract_eq_contract_comp]
--   refine ⟨S ∩ (R ∪ K.E ∩ S ∩ {e | ∀ (x : α), K.Inc x e → e ∈ S → x ∈ T} ∩ n.contractSet),
--     T ∩ n.toFun ⁻¹' U, _, _, rfl⟩
