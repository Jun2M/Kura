import Kura.Operation.Minor2
import Kura.Operation.Simple

open Set Function Graph Sym2
variable {α β α' α'' β' : Type*} {u v w x y z : Set α} {e f : Sym2 (Set α)}
  {G H : Graph (Set α) (Sym2 (Set α))} {G' H' : Graph (Set α') (Sym2 (Set α'))} {u' v' w' : Set α'}

namespace Graph

@[simps! vertexSet edgeSet]
noncomputable def SimpMinor (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) : Graph (Set α) (Sym2 (Set α)) :=
  G / C |>.simplify

scoped infix:50 " // " => Graph.SimpMinor

@[simp]
theorem simpMinor_isLink (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G // C).IsLink e x y ↔  e = s(x, y) ∧ x ≠ y ∧ (G / C).Adj x y := by
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

theorem simpMinor_adj (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G // C).Adj x y ↔ x ≠ y ∧ (G / C).Adj x y := by
  simp_rw [Adj, simpMinor_isLink]
  rw [exists_eq_left, ← Graph.Adj]

instance simpMinor_isSimpleCanonical (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    SimpleCanonical (G // C) := instSimpleCanonicalSimplify

instance instSimpMinorVxSetFinite (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) [Finite V(G)] :
    Finite V(G // C) := by
  unfold SimpMinor
  apply instSimplifyVxSetFinite

instance instSimpMinorEdgeSetFinite (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) [Finite E(G)] :
    Finite E(G // C) := by
  unfold SimpMinor
  apply instSimplifyFinite

@[simp]
def commonNeighbors (G : Graph (Set α) (Sym2 (Set α))) (u v : Set α) : Set (Set α) :=
  {w | G.Adj u w ∧ G.Adj v w}

@[simp]
lemma simplify_edgeSet_ncard_of_loopless_and_toSym2_preserves_nonloop
    (H : Graph (Set α) (Sym2 (Set α))) [H.IsLoopless]
    (h_tosym2_nonloop : ∀ (e : Sym2 (Set α)) (he : e ∈ E(H)), ¬(H.toSym2 e he).IsDiag)
    [Finite E(H)] :
    E(H.simplify).ncard = (Set.image (fun (eSub : E(H)) => H.toSym2 eSub.val eSub.property) E(H).toSet).ncard := by
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
