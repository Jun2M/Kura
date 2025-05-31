import Kura.Operation.Minor2
import Kura.Operation.Simple

open Set Function Graph Sym2
variable {α β α' α'' β' : Type*} {u v w x y z : Set α} {e f : Sym2 (Set α)}
  {G H : Graph (Set α) (Sym2 (Set α))} {G' H' : Graph (Set α') (Sym2 (Set α'))} {u' v' w' : Set α'}

namespace Graph

@[simps! vertexSet edgeSet]
noncomputable def SimpMinor (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    Graph (Set α) (Sym2 (Set α)) :=
  G / C |>.simplify

scoped infix:50 " // " => Graph.SimpMinor

variable {C : Set (Sym2 (Set α))}

@[simp]
theorem simpMinor_isLink : (G // C).IsLink e x y ↔  e = s(x, y) ∧ x ≠ y ∧ (G / C).Adj x y := by
  simp only [SimpMinor, isLink_iff_eq, Simplify_edgeSet, SetContract_edgeSet, mem_diff, mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq, toSym2_eq_pair_iff, SetContract_isLink, exists_and_left, exists_prop,
    ne_eq]
  rw [and_congr_right_iff, and_congr_right_iff]
  rintro rfl hne
  refine ⟨fun ⟨s, hsC, ⟨hs, _⟩, u, hx, v, hy, hbtw⟩ ↦ ?_, fun ⟨e, hbtw⟩ ↦ ?_⟩
  · use s
    rw [← hx, ← hy]
    simp only [SetContract_isLink, hsC, not_false_eq_true, true_and]
    use u, rfl, v, rfl, hbtw
  · have := hbtw.edge_mem.1
    simp at this
    rw [SetContract_isLink] at hbtw
    exact ⟨e, hbtw.1, ⟨this, hbtw.1⟩, hbtw.2⟩

theorem simpMinor_adj : (G // C).Adj x y ↔ x ≠ y ∧ (G / C).Adj x y := by
  simp_rw [Adj, simpMinor_isLink]
  rw [exists_eq_left, ← Graph.Adj]

instance simpMinor_isSimpleCanonical : SimpleCanonical (G // C) := instSimpleCanonicalSimplify

instance instSimpMinorVxSetFinite [Finite V(G)] : Finite V(G // C) := by
  unfold SimpMinor
  apply instSimplifyVxSetFinite

instance instSimpMinorEdgeSetFinite [Finite E(G)] : Finite E(G // C) := by
  unfold SimpMinor
  apply instSimplifyFinite

lemma edgeSet_ncard_simpMinor_singleton [Finite E(G)] [G.SimpleCanonical] [DecidableEq (Set α)]
    (hs_mem : s(x, y) ∈ E(G)) (hs_ne_diag : x ≠ y) :
    E(G // {s(x, y)}).ncard = E(G).ncard - 1 - (N(G, x) ∩ N(G, y)).ncard := by
  classical
  let C := Set.singleton s(x, y)
  let H := G / C
  rw [SimpMinor] -- Goal is E(H.simplify).ncard = ...
  -- We need to show Set.ncard {p : Sym2 (V(H)) | ¬p.IsDiag ∧ H.Adj p.fst p.snd} = RHS
  -- This will be done by partitioning edges of G and relating them to adjacencies in H.

  let contract_vertices : Set (Set α) := {x, y}
  let merged_vertex : Set α := x ∪ y -- Placeholder, formal def below

  -- Formal definition of merged_vertex based on SetContract logic
  -- We'll need to prove merged_vertex_formal = x ∪ y later under appropriate conditions
  let merged_vertex_formal : Set α := ⋃₀ (G ↾ C).Component x -- x here is the lemma argument x

  have component_sUnion_eq_merged_vertex (v_orig_arg : Set α) (hv_mem_contract_vertices : v_orig_arg ∈ contract_vertices) :
      (⋃₀ (G ↾ C).Component v_orig_arg) = merged_vertex_formal := by
    sorry

  have component_sUnion_eq_self_if_not_contracted (v_orig : Set α) (hv_not_mem_contract_vertices : v_orig ∉ contract_vertices) :
      (⋃₀ (G ↾ C).Component v_orig) = v_orig := by
    sorry

  have h_vx_H : V(H) = insert merged_vertex_formal (sdiff V(G) contract_vertices) := by
    ext S_H_vx -- S_H_vx is a vertex of H, so it is of type Set α
    simp_rw [setContract_vertexSet, mem_image, Set.mem_insert_iff, sdiff_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨v_G_orig, hv_G_orig_mem_VG, h_SH_eq_sUnion_comp_vG⟩
      rw [←h_SH_eq_sUnion_comp_vG] -- S_H_vx = ⋃₀ (G ↾ C).Component v_G_orig
      by_cases hv_G_orig_mem_contract_vertices : v_G_orig ∈ contract_vertices
      · rw [component_sUnion_eq_merged_vertex v_G_orig hv_G_orig_mem_contract_vertices]
        exact Or.inl rfl
      · rw [component_sUnion_eq_self_if_not_contracted v_G_orig hv_G_orig_mem_contract_vertices]
        refine Or.inr ?_
        exact ⟨hv_G_orig_mem_VG, hv_G_orig_mem_contract_vertices, rfl⟩
    · rintro (rfl | ⟨v_G_orig, ⟨hv_G_orig_mem_VG, hv_G_orig_not_mem_contract_vertices⟩, h_SH_eq_vG_orig⟩)
      · -- Case 1: S_H_vx = merged_vertex_formal
        rw [merged_vertex_formal] -- merged_vertex_formal is ⋃₀ (G↾C).Component x
        -- We need to show ∃ v_G_orig ∈ V(G), merged_vertex_formal = ⋃₀ (G↾C).Component v_G_orig
        -- Choose v_G_orig = x. We need x ∈ V(G).
        have x_mem_VG : x ∈ V(G) := Graph.fst_mem_vertexSet_of_mem_edgeSet hs_mem
        use x
        exact ⟨x_mem_VG, rfl⟩
      · -- Case 2: S_H_vx = v_G_orig where v_G_orig is not x or y
        rw [h_SH_eq_vG_orig, ← component_sUnion_eq_self_if_not_contracted v_G_orig hv_G_orig_not_mem_contract_vertices]
        use v_G_orig
        exact ⟨hv_G_orig_mem_VG, rfl⟩

  have h_adj_H_UU : ¬ H.Adj merged_vertex_formal merged_vertex_formal := by
    intro h_adj_UU;
    rcases h_adj_UU with ⟨e, h_is_link_H_UU⟩
    -- Definition of IsLink for SetContract (G/C):
    -- (G/C).IsLink e V W ↔ e ∉ C ∧ ∃ v_orig w_orig, (map G C v_orig) = V ∧ (map G C w_orig) = W ∧ G.IsLink e v_orig w_orig
    -- where map G C v = ⋃₀ (G ↾ C).Component v
    rw [SetContract_isLink] at h_is_link_H_UU
    rcases h_is_link_H_UU with ⟨he_notin_C, v_orig, h_map_v_eq_U, w_orig, h_map_w_eq_U, h_G_link_vw⟩

    have map_eq_merged_iff_vxconn_x (v : Set α) : (⋃₀ (G ↾ C).Component v) = merged_vertex_formal ↔ (G ↾ C).VxConnected v x := by
      exact Graph.VxConnected.component_eq_iff_vxConnected (G := (G↾C)) v x -- Assuming this form and that ⋃₀ is handled by component equality.

    have v_orig_conn_x : (G ↾ C).VxConnected v_orig x := (map_eq_merged_iff_vxconn_x v_orig).mp h_map_v_eq_U
    have w_orig_conn_x : (G ↾ C).VxConnected w_orig x := (map_eq_merged_iff_vxconn_x w_orig).mp h_map_w_eq_U

    -- We need to show: (⋃₀ (G ↾ C).Component v) = merged_vertex_formal → v ∈ contract_vertices
    have map_to_merged_implies_in_contract_vertices (v : Set α) (h_map_eq_U : (⋃₀ (G ↾ C).Component v) = merged_vertex_formal) : v ∈ contract_vertices := by
      -- This relies on: map G C v = map G C x → (G↾C).VxConnected v x (from map_eq_merged_iff_vxconn_x below, sorried)
      -- And (G↾C).VxConnected v x → v ∈ contract_vertices (from vxconn_in_GC_means_mem_cv below, sorried)
      sorry

    have v_orig_in_cv : v_orig ∈ contract_vertices := map_to_merged_implies_in_contract_vertices v_orig h_map_v_eq_U
    have w_orig_in_cv : w_orig ∈ contract_vertices := map_to_merged_implies_in_contract_vertices w_orig h_map_w_eq_U

    -- Assuming G.isLink_iff_eq_ne exists from SimpleCanonical G, e.g. (SimpleCanonical.isLink_iff_eq_ne G)
    rw [(G.isLink_iff_eq_ne (G:=G))] at h_G_link_vw
    rcases h_G_link_vw with ⟨rfl, h_v_neq_w⟩ -- Now e = s(v_orig, w_orig)

    have s_vo_wo_eq_sxy : s(v_orig, w_orig) = s(x,y) := by
      simp only [contract_vertices, Set.mem_insert_iff, Set.mem_singleton_iff] at v_orig_in_cv w_orig_in_cv
      rcases v_orig_in_cv with (vx | vy) <;> rcases w_orig_in_cv with (wx | wy)
      · -- v_orig = x, w_orig = x
        rw [vx, wx] at h_v_neq_w; contradiction
      · -- v_orig = x, w_orig = y
        rw [vx, wy]; simp
      · -- v_orig = y, w_orig = x
        rw [vy, wx]; simp [Sym2.eq_swap]
      · -- v_orig = y, w_orig = y
        rw [vy, wy] at h_v_neq_w; contradiction

    rw [s_vo_wo_eq_sxy] at he_notin_C
    simp only [Set.mem_singleton_iff, not_true_eq_false, iff_false] at he_notin_C
    exact he_notin_C

  have h_adj_H_U_v (v_H : Set α) (hv_H_is_orig_from_G_non_contracted: ∃ v_G ∈ (sdiff V(G) contract_vertices), v_H = v_G) :
      H.Adj merged_vertex_formal v_H ↔ (∃ v_G ∈ (sdiff V(G) contract_vertices), v_H = v_G ∧ (G.Adj x v_G ∨ G.Adj y v_G)) := by
    sorry

  have h_adj_H_v_w (v_H w_H : Set α) (hv_H_is_orig: ∃ v_G ∈ (sdiff V(G) contract_vertices), v_H = v_G) (hw_H_is_orig: ∃ w_G ∈ (sdiff V(G) contract_vertices), w_H = w_G) :
      H.Adj v_H w_H ↔ (∃ v_G w_G, v_H = v_G ∧ w_H = w_G ∧ v_G ∈ (sdiff V(G) contract_vertices) ∧ w_G ∈ (sdiff V(G) contract_vertices) ∧ v_G ≠ w_G ∧ G.Adj v_G w_G) := by
    sorry

  -- The proof continues by counting elements in {p : Sym2 (V(H)) | ¬p.IsDiag ∧ H.Adj p.fst p.snd}
  -- based on h_vx_H, h_adj_H_UU, h_adj_H_U_v, and h_adj_H_v_w.
  -- This involves partitioning the edges of G and seeing how they contribute to adjacencies in H.
  sorry

lemma mapVx_apply_singleton_contract (G_graph : Graph (Set α) (Sym2 (Set α)))
    (s_ep1 s_ep2 : Set α) (hs_ne_diag : s_ep1 ≠ s_ep2) (hs_mem : Sym2.mk s_ep1 s_ep2 ∈ E(G_graph))
    (v_node : Set α) :
    (⋃₀ (G_graph ↾ {Sym2.mk s_ep1 s_ep2}).Component v_node) =
      if v_node = s_ep1 ∨ v_node = s_ep2 then s_ep1 ∪ s_ep2 else v_node := by
  sorry

-- Helper lemmas moved from Minor2.lean (or adapted for this context)

-- Lemma: G / C is loopless if G is loopless and C contains no loops.
lemma SetContract_IsLoopless_for_SimpMinor (G_graph : Graph (Set α) (Sym2 (Set α))) (C_set : Set (Sym2 (Set α)))
    [G_graph.IsLoopless] (hC_no_loops : ∀ c ∈ C_set, ¬c.IsDiag) :
    (G_graph / C_set).IsLoopless := by
  sorry

-- Lemma: Relates toSym2 of contracted graph to mapped original endpoints for SimpleCanonical graphs.
lemma toSym2_of_SetContract_SimpleCanonical_eq_map_endpoints_for_SimpMinor
    (G_graph : Graph (Set α) (Sym2 (Set α))) (C_set : Set (Sym2 (Set α)))
    [G_graph.SimpleCanonical] (e_edge : Sym2 (Set α)) (he_GC : e_edge ∈ E(G_graph / C_set)) :
    (G_graph / C_set).toSym2 e_edge he_GC =
      s((⋃₀ (G_graph ↾ C_set).Component (Quot.out e_edge).1), (⋃₀ (G_graph ↾ C_set).Component (Quot.out e_edge).2)) := by
  sorry

-- Lemma: If e = s(x,y) ≠ s_edge is a non-loop edge in a SimpleCanonical graph,
-- its endpoints (x,y) remain distinct after contracting s_edge.
lemma map_vertex_ne_of_ne_endpoints_and_edge_ne_contracted_edge_for_SimpMinor
    (G_graph : Graph (Set α) (Sym2 (Set α))) (s_param_edge : Sym2 (Set α))
    (s_ep1 s_ep2 : Set α) (hs_endpoints_match : Quot.out s_param_edge = (s_ep1, s_ep2))
    (x_node y_node : Set α)
    [G_graph.SimpleCanonical] (hs_ne_diag_s : ¬s_param_edge.IsDiag) (hs_mem_s : s_param_edge ∈ E(G_graph))
    (h_edge_is_xy_mem : s(x_node, y_node) ∈ E(G_graph)) (h_xy_ne_diag : ¬(s(x_node, y_node)).IsDiag)
    (h_edge_xy_ne_s : s(x_node, y_node) ≠ s_param_edge) :
    (⋃₀ (G_graph ↾ {s_param_edge}).Component x_node) ≠ (⋃₀ (G_graph ↾ {s_param_edge}).Component y_node) := by
  sorry

-- Main counting lemma for the effect of simplify after a single edge contraction.
lemma ncard_image_map_endpoints_post_contract_singleton_for_SimpMinor
    (G_graph : Graph (Set α) (Sym2 (Set α)))
    (s_param_edge : Sym2 (Set α)) (s_ep1 s_ep2 : Set α) (hs_endpoints_match : Quot.out s_param_edge = (s_ep1, s_ep2))
    [G_graph.SimpleCanonical] [DecidableEq (Set α)]
    [Finite E(G_graph)] [DecidablePred (· ∈ E(G_graph))] [DecidableEq (Sym2 (Set α))]
    (hs_mem_s : s_param_edge ∈ E(G_graph)) (hs_ne_diag_s : ¬s_param_edge.IsDiag) :
    (Set.image (fun (e_map : Sym2 (Set α)) =>
      s((⋃₀ (G_graph ↾ {s_param_edge}).Component (Quot.out e_map).1),
        (⋃₀ (G_graph ↾ {s_param_edge}).Component (Quot.out e_map).2)))
      (E(G_graph) \ {s_param_edge})).ncard =
    (E(G_graph).ncard - (if hs_mem_s then 1 else 0)) - (N(G_graph, s_ep1) ∩ N(G_graph, s_ep2)).ncard := by
  sorry

lemma edgeSet_ncard_simpMinor_singleton (G_main : Graph (Set α) (Sym2 (Set α))) (s_edge : Sym2 (Set α))
    [Finite E(G_main)] [G_main.SimpleCanonical]
    [DecidablePred (· ∈ E(G_main))] [DecidableEq (Sym2 (Set α))]
    [DecidableEq (Set α)]
    (hs_mem : s_edge ∈ E(G_main)) (hs_ne_diag : ¬s_edge.IsDiag) :
    E(G_main // {s_edge}).ncard = E(G_main).ncard - 1 - (N(G_main, (Quot.out s_edge).1) ∩ N(G_main, (Quot.out s_edge).2)).ncard := by
  let H := G_main / {s_edge}
  have hH_edge_set : E(H) = E(G_main) \ {s_edge} := SetContract_edgeSet G_main {s_edge}

  have hH_IsLoopless : H.IsLoopless := by
    apply SetContract_IsLoopless_for_SimpMinor G_main {s_edge}
    · exact SimpleCanonical.toIsLoopless G_main
    · intro c hc_mem_singleton; rw [mem_singleton_iff] at hc_mem_singleton
      rw [hc_mem_singleton]; exact hs_ne_diag

  let s_ep1 := (Quot.out s_edge).1
  let s_ep2 := (Quot.out s_edge).2
  have hs_endpoints_match : Quot.out s_edge = (s_ep1, s_ep2) := Quot.out_eq_mk s_edge -- Using Quot.out_eq_mk

  have H_toSym2_transformed (e' : Sym2 (Set α)) (he'H : e' ∈ E(H)) :
      (H.toSym2 e' he'H) = s((⋃₀ (G_main ↾ {s_edge}).Component (Quot.out e').1), (⋃₀ (G_main ↾ {s_edge}).Component (Quot.out e').2)) := by
    exact toSym2_of_SetContract_SimpleCanonical_eq_map_endpoints_for_SimpMinor G_main {s_edge} e' he'H

  have transformed_edges_are_non_loops (e' : Sym2 (Set α)) (he'H : e' ∈ E(H)) :
      ¬((H.toSym2 e' he'H)).IsDiag := by
    rw [H_toSym2_transformed e' he'H, Sym2.isDiag_iff_proj_eq]
    have heG_mem : e' ∈ E(G_main) := by { rw [hH_edge_set] at he'H; exact he'H.1 }
    have he_ne_s : e' ≠ s_edge := by { rw [hH_edge_set] at he'H; exact he'H.2 }
    have he_ne_diag : ¬ e'.IsDiag := G_main.not_isDiag_of_mem_edgeSet e' heG_mem -- from G_main.SimpleCanonical.loopless
    exact map_vertex_ne_of_ne_endpoints_and_edge_ne_contracted_edge_for_SimpMinor G_main s_edge s_ep1 s_ep2 hs_endpoints_match (Quot.out e').1 (Quot.out e').2
      hs_ne_diag hs_mem heG_mem he_ne_diag he_ne_s

  rw [SimpMinor] -- E((G_main / {s_edge}).simplify)
  -- We need a lemma: E(H.simplify).ncard = ncard_of_image_of_H_toSym2 when H is loopless and H.toSym2 produces non-loops
  -- This is essentially what ncard_simplify_eq_ncard_image_mapped_endpoints aims to be, but its signature needs adjustment.

  -- Instead of ncard_simplify_eq_ncard_image_mapped_endpoints, we directly use the fact that
  -- E(H.simplify).ncard = (Set.image (fun (eSub : E(H)) => H.toSym2 eSub.val eSub.property) E(H).toSet).ncard
  -- This step requires a lemma like: Simplify_edgeSet_ncard_eq_image_toSym2_ncard (H : Graph _ _) [H.IsLoopless] (h_nonloop_image) : E(H.simplify).ncard = (image H.toSym2 E(H)).ncard
  -- For now, assume this step and proceed to map the image over E(H) to image over E(G_main) \ {s_edge}

  -- Let's assume E(H.simplify).ncard = (Set.image (fun (eSub : Subtype (· ∈ E(H))) => H.toSym2 eSub.val eSub.property) (E(H).toSet)).ncard
  -- This should come from a general property of simplify for loopless graphs where toSym2 image is loopless.

  -- Step 1: Relate E(H.simplify).ncard to the image of H.toSym2 over E(H)
  have ncard_simplify_H : E(H.simplify).ncard = (Set.image (fun (eSub : E(H)) => H.toSym2 eSub.val eSub.property) E(H).toSet).ncard := by
    -- This would use a more general version of the simplify_edgeSet_ncard_of_loopless_and_toSym2_preserves_nonloop lemma
    -- from the previous attempt, adapted for the toSym2 of H.
    sorry
  rw [ncard_simplify_H]

  -- Step 2: Transform the image over E(H) to an image over E(G_main) \ {s_edge}
  let map_fn_on_G_edges := fun (e_map : Sym2 (Set α)) =>
      s((⋃₀ (G_main ↾ {s_edge}).Component (Quot.out e_map).1), (⋃₀ (G_main ↾ {s_edge}).Component (Quot.out e_map).2))

  have image_H_eq_image_G_diff :
      (Set.image (fun (eSub : E(H)) => H.toSym2 eSub.val eSub.property) E(H).toSet) =
      Set.image map_fn_on_G_edges (E(G_main) \ {s_edge}) := by
    ext t; simp only [Set.mem_image, Set.mem_toSetE, Graph.E, hH_edge_set]
    constructor
    · rintro ⟨⟨e', he'H_prop⟩, h_eq⟩; use e', he'H_prop; rw [H_toSym2_transformed e' he'H_prop, h_eq]
    · rintro ⟨e', he_G_diff_s_prop, h_eq⟩; use ⟨e', he_G_diff_s_prop⟩; rw [H_toSym2_transformed e' he_G_diff_s_prop, h_eq]
  rw [image_H_eq_image_G_diff]

  -- Step 3: Apply the main counting lemma from Minor2.lean
  rw [ncard_image_map_endpoints_post_contract_singleton_for_SimpMinor G_main s_edge s_ep1 s_ep2 hs_endpoints_match hs_mem hs_ne_diag]
  simp only [hs_mem, if_true] -- to make (if hs_mem then 1 else 0) into 1

end Graph
