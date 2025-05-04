import Kura.Operation.Hom


open Set Function
variable {α ε α' α'' ε' : Type*} {G G' H H' : Graph α ε} {u v w : α} {e f : ε} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set ε}


class Graph.IsLoopless (G : Graph α ε) : Prop where
  loopless x : ¬ G.Adj x x

instance Graph.instLooplessGraphic : Graph.GraphicFunction IsLoopless where
  presv_isom G G' h := by
    ext
    obtain ⟨g, hg⟩ := h.symm
    obtain ⟨f, hf⟩ := h
    refine ⟨fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩, fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩⟩
    · exact hloop.loopless (g x) ⟨g.edgeFun e, hbtw.isIsomOn hg hbtw.edge_mem hbtw.vx_mem_left hbtw.vx_mem_right⟩
    · exact hloop.loopless (f x) ⟨f.edgeFun e, hbtw.isIsomOn hf hbtw.edge_mem hbtw.vx_mem_left hbtw.vx_mem_right⟩

class Graph.IsSimple (G : Graph α ε) : Prop extends IsLoopless G where
  no_multi_edges e f he hf : G.toSym2 e he = G.toSym2 f hf → e = f

instance Graph.instSimpleGraphic : Graph.GraphicFunction IsSimple where
  presv_isom G G' h := by
    ext
    refine ⟨fun hsimple ↦ ?_, fun hsimple ↦ ?_⟩
    · exact {
        loopless := (instLooplessGraphic.presv_isom G G' h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf h ↦ by
          sorry}
    · exact {
        loopless := (instLooplessGraphic.presv_isom G G' h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf h ↦ by
          sorry}

/-- The graph induced by a simple graph -/
@[simps]
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  V := univ
  E := G.edgeSet
  Inc₂ e x y := s(x,y) = e ∧ G.Adj x y
  inc₂_symm e x y := by simp [Sym2.eq_swap, SimpleGraph.adj_comm]
  vx_mem_left_of_inc₂ e x y := by simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, hx, he⟩ ↦ by simp [he, ← hx]⟩
    induction' e with x y
    use x, y
    simpa using he
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨rfl, he⟩ := h1
    obtain ⟨heq, he'⟩ := h2
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto

variable {G' H' : SimpleGraph α}

@[simp]
lemma SimpleGraph.toGraph_adj : (SimpleGraph.toGraph G').Adj = G'.Adj := by
  ext x y
  simp_rw [Graph.Adj, toGraph_inc₂, exists_eq_left']

@[simp]
lemma SimpleGraph.toGraph_inj : G'.toGraph = H'.toGraph ↔ G' = H' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  ext x y
  rw [← toGraph_adj, ← toGraph_adj, h]

namespace Graph

@[simps]
def toSimpleGraph (G : Graph α ε) : SimpleGraph G.V where
  Adj a b := a ≠ b ∧ G.Adj a b
  symm a b hab := by simpa only [ne_eq, eq_comm, adj_comm] using hab

@[simps!]
def Simplify (G : Graph α ε) : Graph α (Sym2 α) :=
  oftoSym2 G.V {s | ∃ (e : ε) (he : e ∈ G.E), G.toSym2 e he = s ∧ ¬ s.IsDiag}
    (fun e _ ↦ e) (fun e x ⟨f, hf, h, hdiag⟩ hx ↦ by subst e; exact vx_mem_of_toSym2 hx)

@[simp]
lemma simplify_adj : (Simplify G).Adj u v ↔ u ≠ v ∧ G.Adj u v := by
  simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop,
    exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, ← ne_eq]
  rw [and_comm, and_congr_right_iff]
  exact fun hne ↦ exists_congr fun e ↦ and_iff_right_iff_imp.mpr (Inc₂.edge_mem ·)

instance instSimpleSimplify : IsSimple (Simplify G) where
  loopless x := by
    simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop,
      exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, not_true_eq_false, and_false,
      not_false_eq_true]
  no_multi_edges e f he hf h := by
    simpa only [Simplify, mem_setOf_eq, oftoSym2_tosym2] using h

lemma forall_Simplify {ε : Type u_1} (F : {α : Type u_1} → {ε : Type u_1} → Graph α ε → Prop)
    [hF : GraphicFunction F] [Nonempty α] [Nonempty ε] [Nonempty (Sym2 α)]
    (h : ∀ (G' : Graph α (Sym2 α)), G'.IsSimple → (∀ (e) (he : e ∈ G'.E), G'.toSym2 e he = e) → F G') :
    ∀ (G : Graph α ε), F G := fun G => by
    rw [hF.presv_isom G G.Simplify sorry]
    exact h G.Simplify instSimpleSimplify sorry

end Graph
