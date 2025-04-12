import Kura.Operation.Subgraph
import Kura.Operation.Map


open Set Function
variable {α β α' α'' : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph

/-- `Contract G φ C` contracts the edges in set `C` of graph `G`,
    mapping the resulting vertices according to function `φ`.

    This operation creates a new graph where:
    1. Edges in set `C` are removed
    2. Vertices are relabeled according to the mapping function `φ`

    This is the fundamental operation for creating graph minors. -/
noncomputable def Contract (G : Graph α β) (φ : α → α') (C : Set β) : Graph α' β :=
  (G.vxMap φ){G.E \ C}

notation:1023 G "/["φ"]" C => Graph.Contract G φ C

/- lemmas about Contract -/
namespace Contract


/-- A function `φ` is valid on a graph `G` with respect to a set of edges `C` if
    it maps two vertices to the same vertex precisely when they are connected
    in the subgraph induced by the edges in `C`.

    This property ensures that contraction preserves the structure of the graph
    in a well-defined way. -/
def ValidIn (G : Graph α β) (φ : α → α') (C : Set β) :=
  ∀ ⦃x y⦄, x ∈ G.V → y ∈ G.V → (φ x = φ y ↔ G{C}.Connected x y)

variable {φ τ : α → α'} {C D : Set β}

@[simp]
lemma map_mem (φ : α → α') (C : Set β) (hx : x ∈ G.V) : φ x ∈ (G /[φ] C).V := by
  use x

lemma map_eq_of_reflAdj (hC : ValidIn G φ C) (hradj : G{C}.reflAdj x y) : φ x = φ y := by
  obtain h | ⟨rfl, h⟩ := hradj
  · rw [hC h.mem_left h.mem_right]
    exact h.connected
  · rfl

lemma ValidIn.of_inter_eq (hC : ValidIn G φ C) (h : G.E ∩ C = G.E ∩ D) :
    ValidIn G φ D := by
  rwa [ValidIn, ← (G.restrict_eq_restrict_iff C D).mpr h]

lemma toFun_eq_of_inter_eq_fixed_eq (hC : ValidIn G φ C) (hD : ValidIn G τ C)
    (hfixed : ∀ a ∈ G.V, ∃ x ∈ G.V, τ x = φ a ∧ φ x = φ a) : EqOn φ τ G.V := by
  rintro x hx
  obtain ⟨y, hy, htypx, hpypx⟩ := hfixed x hx
  rwa [← htypx, hD hy hx, ← hC hy hx]

lemma toFun_eq_of_inter_eq_fixed_eq' (hC : ValidIn G φ C) (hD : ValidIn G τ D)
    (hinter : G.E ∩ C = G.E ∩ D)
    (hfixed : ∀ a ∈ G.V, ∃ x ∈ G.V, τ x = φ a ∧ φ x = φ a) : EqOn φ τ G.V := by
  rintro x hx
  obtain ⟨y, hy, hτyφx, hφyφx⟩ := hfixed x hx
  rwa [← hτyφx, hD hy hx, ← (G.restrict_eq_restrict_iff C D).mpr hinter, ← hC hy hx]

lemma ValidIn.le (hC : ValidIn G φ C) (hle : H ≤ G) (hE : G.E ∩ C ⊆ H.E) :
    ValidIn H φ C := by
  intro x y hx hy
  rw [hC (vx_subset_of_le hle hx) (vx_subset_of_le hle hy)]
  exact (restrict_Connected_iff_restrict_Connected_of_le hle hE hx).symm


/-- Given a set of edges `S` in a graph, this lemma shows that there exists a valid
    contraction function and corresponding contracted edge set that precisely equals `S`.

    This is useful for showing that any set of edges can be validly contracted. -/
lemma exists_rep_of_contractSet (S : Set β) : ∃ (φ : α → α), ValidIn G φ S := by
  classical
  -- Get a representative function for the connected components
  obtain ⟨φ, hid, hrel, heq⟩ := Partition.nonempty_repFun (ConnectedPartition (G{S}))
  use φ
  -- Show that φ is a valid contraction function with respect to S
  intro x y hx hy
  constructor
  · intro h_eq_φ
    obtain hconnx := hrel x hx
    obtain hconny := hrel y hy
    simp only [ConnectedPartition, rel_ofRel'_eq] at hconnx hconny
    refine (hconnx.trans ?_).trans hconny.symm
    rw [h_eq_φ]
    refine Connected.refl ?_
    exact hconny.mem_right
  · intro h_connected
    apply heq _ _
    simp only [ConnectedPartition, rel_ofRel'_eq]
    exact h_connected

noncomputable def SubgraphContractFun (G : Graph α β) (S : Set β) :=
  fun x ↦ G{S}[{y | G{S}.Connected x y}]

lemma SubgraphContractFun.ValidIn (S : Set β) : ValidIn G (SubgraphContractFun G S) S := by
  rintro x y hx hy
  simp +contextual only [induce_eq_induce_iff, ext_iff_simp, iff_def, SubgraphContractFun]
  constructor
  · rintro h
    obtain ⟨H1, H2⟩ := h y
    exact H2 (Connected.refl hy)
  · rintro hconn z
    exact ⟨hconn.symm.trans, hconn.trans⟩




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
lemma V : (G /[φ] C).V = φ '' G.V := rfl

@[simp]
lemma E : (G /[φ] C).E = G.E \ C := by
  simp only [Contract, vxMap, restrict_E, inter_eq_right]
  tauto_set

lemma E_subset : (G /[φ] C).E ⊆ G.E := by
  simp only [E]
  tauto_set

@[simp]
lemma Inc {x : α'} : (G /[φ] C).Inc e x ↔ ∃ v, φ v = x ∧ G.Inc e v ∧ e ∉ C := by
  simp +contextual only [Contract, vxMap_inc_iff, restrict_inc, mem_diff, iff_def]
  constructor
  · rintro ⟨⟨v, rfl, hv⟩, hin, hnin⟩
    use v
    tauto
  · rintro ⟨v, rfl, hinc, hnin⟩
    use ⟨v, rfl, hinc⟩, hinc.edge_mem, hnin

lemma inc₂_of_inc₂ (hbtw : G.Inc₂ e x y) (hnin : e ∉ C) : (G /[φ] C).Inc₂ e (φ x) (φ y) := by
  simp only [Contract, restrict_inc₂, vxMap.Inc₂, mem_diff, hbtw.edge_mem, hnin,
    not_false_eq_true, and_self, and_true]
  use x, rfl, y

@[simp]
lemma Inc₂ {x' y' : α'} : (G /[φ] C).Inc₂ e x' y' ↔ ∃ x, φ x = x' ∧ ∃ y, φ y = y' ∧
    G.Inc₂ e x y ∧ e ∉ C:= by
  simp +contextual only [Contract, restrict_inc₂, vxMap.Inc₂, mem_diff, iff_def,
    not_false_eq_true, and_true, implies_true, forall_exists_index, and_imp, true_and]
  rintro x rfl y rfl hbtw hnin
  exact ⟨⟨x, rfl, y, rfl, hbtw⟩, hbtw.edge_mem⟩

lemma inc₂ (φ : α → α') (he : e ∉ C) (hbtw : G.Inc₂ e u v) :
    (G /[φ] C).Inc₂ e (φ u) (φ v) := by
  rw [Contract, restrict_inc₂]
  exact ⟨hbtw.vxMap_of_inc₂ φ, hbtw.edge_mem, he⟩

@[simp]
lemma contract_eq_contract_iff :
    (G /[φ] C) = (G /[φ] D) ↔ G.E \ C = G.E \ D := by
  constructor <;> rintro hE
  · apply_fun Graph.E at hE
    simpa using hE
  · have hE' := Set.ext_iff.mp hE
    simp only [mem_diff, and_congr_right_iff] at hE'
    apply ext_inc
    · simp
    · ext e
      specialize hE' e
      simpa  [E, mem_diff, and_congr_right_iff]
    · intro e x
      simp only [Inc]
      constructor <;> rintro ⟨x, rfl, hinc, hnin⟩ <;> use x, rfl, hinc
      · rwa [← hE' _ hinc.edge_mem]
      · rwa [hE' _ hinc.edge_mem]

@[simp]
lemma contract_restrict_eq_restrict_contract {S : Set β} :
    (G /[φ] C){S} = (G{S ∪ (G.E ∩ C)} /[φ] C) := by
  apply ext_inc
  · simp
  · simp only [restrict_E, E, mem_inter_iff, mem_diff, mem_union]
    tauto_set
  · simp only [restrict_inc, Inc, mem_union, mem_inter_iff]
    tauto

-- @[simp]
-- lemma contract_induce_eq_induce_contract {S : Set α'} : (G /[φ] C)[S] =
--     (G[φ ⁻¹' S]/(φ.confine hvalid (φ ⁻¹' S))) := by
--   ext x e
--   · simp only [induce_V, contract_V, mem_inter_iff, mem_image, ContractSys.confine, mem_preimage]
--     constructor
--     · rintro ⟨⟨v, hv, rfl⟩, hvS⟩
--       use v, ⟨hv, hvS⟩
--       have : m.toFun v ∈ m.toFun ⁻¹' S := by
--         simp only [mem_preimage, m.idem, hvS]
--       simp only [this, ↓reduceIte]
--     · rintro ⟨v, ⟨hv, hvS⟩, rfl⟩
--       have : m.toFun v ∈ m.toFun ⁻¹' S := by
--         simp only [mem_preimage, m.idem, hvS]
--       simp only [this, ↓reduceIte, hvS, and_true]
--       use v
--   · simp only [induce_E, contract_E, contract_inc, forall_exists_index, and_imp, mem_inter_iff,
--     mem_diff, mem_setOf_eq, ContractSys.confine, mem_preimage, not_and, not_exists]
--     constructor
--     · rintro ⟨⟨hx, hnin⟩, hS⟩
--       use ⟨hx, ?_⟩
--       exact fun a x_1 a_1 a_2 ↦ hnin a
--       rintro v hinc
--       exact hS (m.toFun v) v rfl hinc hnin
--     · rintro ⟨⟨hx, hS⟩, hnS⟩
--       simp only [m.idem] at hnS
--       use ⟨hx, ?_⟩
--       · rintro a b rfl hinc hnin
--         exact hS b hinc
--       · rintro hin
--         obtain ⟨v, hinc⟩ := G.exists_vertex_inc hx
--         exact hnS hin v hinc (hS v hinc)
--   · simp only [induce_inc, contract_inc, forall_exists_index, and_imp, ContractSys.confine,
--     mem_preimage, mem_setOf_eq, not_and, not_exists]
--     constructor
--     · rintro ⟨⟨v, rfl, hinc, hnin⟩, hS⟩
--       use v
--       have : m.toFun v ∈ m.toFun ⁻¹' S := by
--         simp only [mem_preimage, m.idem, (hS (m v) v rfl hinc hnin)]
--       simp only [this, ↓reduceIte, true_and]; clear this
--       use ⟨hinc, ?_⟩
--       · exact fun a x a_1 a_2 ↦ hnin a
--       · rintro x hinc
--         exact hS (m.toFun x) x rfl hinc hnin
--     · rintro ⟨y, rfl, ⟨hinc, hS⟩, hnS⟩
--       simp only [m.idem] at hnS
--       refine ⟨?_, ?_⟩
--       · refine ⟨y, ?_, hinc, ?_⟩
--         · have : m.toFun y ∈ m.toFun ⁻¹' S := by
--             simp only [mem_preimage, m.idem]
--             exact hS y hinc
--           simp only [this, ↓reduceIte]
--         · rintro hin
--           exact hnS hin y hinc (hS y hinc)
--       · rintro x z rfl hinc hnin
--         exact hS z hinc

end Contract

/- Creators of ContractSys -/

-- /-- Creates a contraction system from a single edge incident to a vertex.

--     Given a vertex `x` incident to edge `e`, this creates a contraction system
--     that contracts edge `e` and maps all vertices incident to `e` to `x`. -/
-- def Inc.contractFun (_hxe : G.Inc x e) [DecidablePred (G.Inc · e)] : α → α :=
--   fun y ↦ if G.Inc y e then x else y

-- lemma Inc.contractFun_validIn (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] :
--     Contract.ValidIn G (Inc.contractFun hxe) {e} := by
--   rintro a b ha hb
--   simp only [contractFun]
--   split_ifs with hainc hbinc hbinc
--   · simp only [true_iff]
--     refine reflAdj.connected ?_
--     refine Inc.reflAdj_of_inc ⟨hainc, rfl⟩ ⟨hbinc, rfl⟩
--   · apply iff_of_false
--     · rintro rfl
--       exact hbinc hxe
--     · have hab : a ≠ b := by
--         rintro rfl
--         exact hbinc hainc
--       rw [Connected.comm, connected_iff_eq_and_mem_no_inc_edge' ?_]
--       tauto
--       · rintro e' he'
--         simp only [restrict_E, mem_inter_iff, mem_singleton_iff] at he'
--         obtain ⟨he, rfl⟩ := he'
--         simp [hbinc]
--   · apply iff_of_false
--     · rintro rfl
--       exact hainc hxe
--     · have hab : a ≠ b := by
--         rintro rfl
--         exact hainc hbinc
--       rw [connected_iff_eq_and_mem_no_inc_edge' ?_]
--       tauto
--       · rintro e' he'
--         simp only [restrict_E, mem_inter_iff, mem_singleton_iff] at he'
--         obtain ⟨he, rfl⟩ := he'
--         simp only [restrict_inc, hainc, mem_singleton_iff, and_true, not_false_eq_true]
--   · rw [connected_iff_eq_and_mem_no_inc_edge' ?_]
--     simp [ha]
--     · rintro e' he'
--       simp only [restrict_E, mem_inter_iff, mem_singleton_iff] at he'
--       obtain ⟨he, rfl⟩ := he'
--       simpa [restrict_inc]

def Inc₂.contractFun (_hexy : G.Inc₂ e x y) [DecidableEq α] : α → α :=
  fun u ↦ if u = y then x else u

lemma Inc₂.contractFun_validIn (hexy : G.Inc₂ e x y) [DecidableEq α] :
    Contract.ValidIn G hexy.contractFun {e} := by
  rintro a b ha hb
  have hsub := G.restrict_E_subset_singleton e
  simp only [contractFun]
  split_ifs with hainc hbinc hbinc
  · subst hainc hbinc
    simp only [true_iff]
    refine reflAdj.connected ?_
    exact reflAdj.of_vxMem hb
  · subst hainc
    rw [connected_iff_reflAdj_of_E_subsingleton hsub, reflAdj.Adj_iff_ne,
      Adj.iff_inc₂_of_E_subsingleton hsub,
      inc₂_iff_inc₂_of_edge_mem_le (restrict_le _ _) (by simp [hsub, hexy.edge_mem]),
      hexy.symm.inc₂_iff_eq_right]
    exact fun a_1 ↦ hbinc a_1.symm
  · subst hbinc
    rw [connected_iff_reflAdj_of_E_subsingleton hsub, reflAdj.Adj_iff_ne,
      Adj.iff_inc₂_of_E_subsingleton hsub,
      inc₂_iff_inc₂_of_edge_mem_le (restrict_le _ _) (by simp [hsub, hexy.edge_mem]),
      hexy.inc₂_iff_eq_left]
    exact fun a_1 ↦ hainc a_1
  · rw [connected_iff_reflAdj_of_E_subsingleton hsub]
    have hnadj : ¬ G{{e}}.Adj a b := by
      rintro ⟨e', hbtw⟩
      simp only [restrict_inc₂, mem_singleton_iff] at hbtw
      obtain ⟨hbtw, rfl⟩ := hbtw
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hexy.eq_or_eq_of_inc₂ hbtw
      · exact hbinc rfl
      · exact hainc rfl
    simp [hnadj, ha]

lemma Inc₂.contractFun_eq_self_of_not_inc [DecidableEq α] (hexy : G.Inc₂ e x y)
    (h : ¬ G.Inc e u) : hexy.contractFun u = u := by
  simp only [contractFun, ite_eq_right_iff]
  rintro rfl
  exact (h hexy.inc_right).elim

@[simp]
lemma Inc₂.contractFun_eq_self_iff [DecidableEq α] (hexy : G.Inc₂ e x y) (hxy : x ≠ y) :
    hexy.contractFun u = u ↔ u ≠ y := by
  simp +contextual [Inc₂.contractFun, hxy]

@[simp]
lemma Inc₂.vx_mem_contract_iff [DecidableEq α] (hexy : G.Inc₂ e x y) :
    u ∈ (G /[hexy.contractFun] {e}).V ↔ u ∈ G.V \ {y} ∪ {x} := by
  simp +contextual only [Contract.V, Inc₂.contractFun, mem_image, union_singleton,
    mem_insert_iff, mem_diff, mem_singleton_iff, iff_def, forall_exists_index, and_imp]
  constructor
  · rintro v hv rfl
    split_ifs with h <;> simp [h, hv]
  · rintro (rfl | ⟨h, hnin⟩)
    · use y, hexy.vx_mem_right, (by simp)
    . use u, h, (by simp [hnin])

namespace Contract
variable {φ : α → α'} {τ : α' → α''} {C D : Set β} {x y : α'}

instance instFinite [h : G.Finite] : (G /[φ] C).Finite where
  vx_fin := Set.Finite.image φ h.vx_fin
  edge_fin := by
    apply Set.Finite.subset (h.edge_fin)
    exact E_subset

lemma reflAdj (hbtw : G.reflAdj u v) (hVd : ValidIn G φ C) : (G /[φ] C).reflAdj (φ u) (φ v) := by
  obtain ⟨e', hbtw'⟩ | ⟨rfl, huv⟩ := hbtw
  · by_cases he : e' ∈ C
    · have : G{C}.Connected u v := by
        apply Inc₂.connected
        rw [restrict_inc₂]
        exact ⟨hbtw', he⟩
      rw [← hVd hbtw'.vx_mem_left hbtw'.vx_mem_right] at this
      rw [this]; clear this
      refine reflAdj.of_vxMem ?_
      use v, hbtw'.vx_mem_right
    · exact (inc₂ φ he hbtw').reflAdj
  · exact reflAdj.of_vxMem (by use u)

lemma connected_of_map_reflAdj (hVd : ValidIn G φ C) (hradj : (G /[φ] C).reflAdj (φ u) (φ v))
    (hu : u ∈ G.V) (hv : v ∈ G.V) : G.Connected u v := by
  have hle := G.restrict_le C
  obtain ⟨e, hbtw⟩ | ⟨heq, hmem⟩ := hradj
  · obtain ⟨he', he, heC⟩ := hbtw.edge_mem; clear he'
    obtain ⟨a, b, hbtwG⟩ := G.exist_inc₂_of_mem he
    have heqeq := (inc₂ φ heC hbtwG).eq_or_eq_of_inc₂ hbtw
    wlog heq : φ a = φ u ∧ φ b = φ v
    · simp only [heq, false_or] at heqeq
      rw [and_comm] at heqeq
      apply this hVd hu hv hle e hbtw he heC b a hbtwG.symm ?_ heqeq
      left
      exact heqeq
    rw [hVd hbtwG.vx_mem_left hu, hVd hbtwG.vx_mem_right hv] at heq
    exact ((heq.1.symm.le hle).trans (hbtwG.connected)).trans (heq.2.le hle)
  · rw [hVd hu hv] at heq
    exact heq.le hle

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

@[simp]
lemma connected_iff (hVd : ValidIn G φ C) (hu : u ∈ G.V) (hv : v ∈ G.V) :
    (G /[φ] C).Connected (φ u) (φ v) ↔ G.Connected u v :=
  ⟨(connnected_of_map_connected hVd · u hu v hv rfl rfl), connected hVd⟩



-- lemma comp_symm_of_inter_eq {n m : ContractSys α β α} (hm : m.validIn G) (hn : n.validIn G)
--     (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet) (v : α) :
--     m (n v) = n v → n (m v) = m v := by
--   rintro h
--   by_cases hv : v ∈ G.V
--   · have : G{n.contractSet}.Connected v (n v) := (hn.map_connected hv).mp
--     rw [(G.restrict_eq_restrict_iff n.contractSet m.contractSet).mpr hinter.symm] at this
--     have := hm.map_eq_of_connected this
--     rw [h] at this
--     rw [this, n.idem]
--   · rw [hm.map_not_mem hv, hn.map_not_mem hv]

-- lemma ContractSys.comp_comm_of_inter_eq {m : ContractSys α β} (hmvalid : m.validIn G)
--     {n : ContractSys α β} (hnvalid : n.validIn G) (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet)
--     (v : α) : m (n v) = n v ↔ n (m v) = m v :=
--     ⟨ContractSys.comp_symm_of_inter_eq hmvalid hnvalid hinter v,
--     ContractSys.comp_symm_of_inter_eq hnvalid hmvalid hinter.symm v⟩

-- lemma ContractSys.toFun_eq_of_comp_eq_of_inter_eq {m : ContractSys α β} (hmvalid : m.validIn G)
--     {n : ContractSys α β} (hnvalid : n.validIn G) (h : ∀ v, n (m v) = m v)
--     (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet) : m.toFun = n.toFun := by
--   ext x
--   by_cases hx : x ∈ G.V
--   · rw [← h]
--     have : G{m.contractSet}.Connected x (m x) := hmvalid.map_connected hx
--     rw [(G.restrict_eq_restrict_iff m.contractSet n.contractSet).mpr hinter] at this
--     exact (hnvalid.map_eq_of_connected this).symm
--   · rw [hmvalid.map_not_mem hx, hnvalid.map_not_mem hx]


-- private lemma connected_restrict_of_reflAdj_restrict_contract (S : Set β)
--     (h : (G/m ~hvalid){S}.reflAdj x y) : G{m.contractSet ∪ S}.Connected x y := by
--   rw [reflAdj_iff_adj_or_eq] at h
--   obtain ⟨e, hinc, h⟩ | ⟨rfl, hin⟩ := h
--   · by_cases hx : x = y
--     · subst x
--       simp only [↓reduceIte] at h
--       obtain ⟨v, hvinc, heq⟩ := h
--       have := heq y hinc
--       subst y
--       refine Relation.TransGen.single ?_
--       apply reflAdj_of_vxMem
--       simp only [restrict_V]
--       exact vx_mem_of_mem_contract hvalid hinc.vx_mem
--     · simp only [hx, ↓reduceIte] at h
--       obtain ⟨⟨y, rfl, hinc, hnin⟩, heS⟩ := hinc
--       obtain ⟨⟨v, rfl, hvinc, _⟩, _⟩ := h
--       have hle := (G.restrict_mono _ (m.contractSet ∪ S) subset_union_left)
--       refine (hvalid.map_connected hinc.vx_mem).symm.le hle |>.trans ?_
--       refine (?_ : G{m.contractSet ∪ S}.Connected y v).trans <| (hvalid.map_connected hvinc.vx_mem).le hle
--       refine Connected.le ?_ (G.restrict_mono _ (m.contractSet ∪ S) subset_union_right)
--       refine Relation.TransGen.single (Adj.reflAdj ?_)
--       use e, ⟨hinc, heS⟩
--       have : y ≠ v := fun a ↦ hx (congrArg m.toFun a)
--       simp only [this, ↓reduceIte]
--       exact ⟨hvinc, heS⟩
--   · refine Relation.TransGen.single (reflAdj_of_vxMem ?_)
--     obtain ⟨v, hv, rfl⟩ := hin
--     simp only [restrict, mem_union, true_and]
--     exact hvalid.map_mem hv

-- lemma Connected.restrict_of_connected_restrict_contract (S : Set β)
--     (h : (G/m ~hvalid){S}.Connected x y) : G{m.contractSet ∪ S}.Connected x y := by
--   induction h with
--   | single hadj => exact connected_restrict_of_reflAdj_restrict_contract hvalid S hadj
--   | tail hconn hadj ih => exact ih.trans
--     <| connected_restrict_of_reflAdj_restrict_contract hvalid S hadj

-- lemma Connected.of_contract (h : (G/m ~hvalid).Connected x y) : G.Connected x y := by
--   convert Connected.restrict_of_connected_restrict_contract hvalid Set.univ (x := x) (y := y) ?_ using 1
--   · rw [eq_comm, restrict_eq_self_iff]
--     exact diff_subset_iff.mp fun ⦃a⦄ a ↦ trivial
--   · convert h
--     rw [restrict_eq_self_iff]
--     exact fun ⦃a⦄ a ↦ trivial

-- private lemma Connected.map_restrict_of_connected_restrict_contract_eq_eq (S : Set β)
--     (h : (G/m ~hvalid){S}.Connected x y) :
--     ∀ u v, m u = x → m v = y → G{m.contractSet ∪ S}.Connected u v := by
--   have := Connected.restrict_of_connected_restrict_contract hvalid S (x := x) (y := y) h
--   rintro u v rfl rfl
--   have hle := (G.restrict_mono _ (m.contractSet ∪ S) subset_union_left)
--   refine (?_ : G{m.contractSet ∪ S}.Connected u (m u)).trans (this.trans ?_)
--   · refine (hvalid.map_connected ?_).le hle
--     have := h.mem
--     simpa only [restrict, map_mem_contract_iff_vx_mem] using this
--   · refine (hvalid.map_connected ?_).le hle |>.symm
--     have := h.mem'
--     simpa only [restrict, map_mem_contract_iff_vx_mem] using this

-- lemma Connected.map_restrict_of_connected_restrict_contract (S : Set β)
--     (h : (G/m ~hvalid){S}.Connected (m x) (m y)) : G{m.contractSet ∪ S}.Connected x y :=
--   Connected.map_restrict_of_connected_restrict_contract_eq_eq hvalid S h _ _ rfl rfl

-- lemma Connected.map_of_connected_contract (h : (G/m ~hvalid).Connected (m x) (m y)) :
--     G.Connected x y := by
--   convert Connected.map_restrict_of_connected_restrict_contract hvalid Set.univ (x := x) (y := y) ?_
--     using 1
--   · simp only [restrict, union_univ, inter_univ, mem_univ, and_true]
--   · convert h
--     rw [restrict_eq_self_iff]
--     exact fun ⦃a⦄ a ↦ trivial

-- lemma connected_contract_restrict_of_restrict_adj (S : Set β)
--     (h : G{m.contractSet ∪ S}.reflAdj x u) :
--     (G/m ~hvalid){S}.Connected (m.toFun x) (m.toFun u) := by
--   by_cases hx : x = u
--   · subst u
--     refine Connected.refl ?_
--     simp only [restrict, map_mem_contract_iff_vx_mem]
--     rw [reflAdj_iff_adj_or_eq] at h
--     obtain ⟨e, hinc, hnin⟩ | ⟨_, hin⟩ := h
--     · have := hinc.vx_mem
--       simpa only [restrict, mem_union] using this
--     · simpa only [restrict, mem_union] using hin
--   · simp only [reflAdj, Adj, hx, ↓reduceIte, false_and, or_false] at h
--     obtain ⟨e, hxinc, huinc⟩ := h
--     obtain ⟨he, hemS⟩ := hxinc.edge_mem
--     rw [← union_diff_self] at hemS
--     obtain hem | ⟨heS, hem⟩ := hemS
--     · have hle := G.restrict_le (m.contractSet ∪ S)
--       rw [hvalid.map_edge hem (hxinc.le hle) (huinc.le hle)]
--       refine Connected.refl ?_
--       simp only [restrict, map_mem_contract_iff_vx_mem]
--       exact (huinc.le hle).vx_mem
--     · refine Relation.TransGen.single ?_
--       rw [reflAdj_iff_adj_or_eq]
--       by_cases heq : m x = m u
--       · right
--         use heq
--         simp only [restrict, map_mem_contract_iff_vx_mem]
--         exact hxinc.vx_mem
--       · left
--         use e, ?_
--         simp only [heq, ↓reduceIte, restrict, contract, heS, and_true]
--         use u, rfl, huinc.1
--         simp only [restrict, contract, heS, and_true]
--         use x, rfl, hxinc.1

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



-- def IsContraction (H G : Graph α β) := ∃ m hm, H = G/m ~hm

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
