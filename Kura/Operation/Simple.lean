import Kura.Operation.Hom


open Set Function
variable {α α' α'' β β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}


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
def toSimpleGraph (G : Graph α β) : SimpleGraph G.V where
  Adj a b := a ≠ b ∧ G.Adj a b
  symm a b hab := by simpa only [ne_eq, eq_comm, adj_comm] using hab

@[simps!]
def Simplify (G : Graph α β) : Graph α (Sym2 α) :=
  oftoSym2 G.V {s | ∃ (e : β) (he : e ∈ G.E), G.toSym2 e he = s ∧ ¬ s.IsDiag}
    (fun e _ ↦ e) (fun e x ⟨f, hf, h, hdiag⟩ hx ↦ by subst e; exact vx_mem_of_toSym2 hx)

@[simp]
lemma simplify_adj : (Simplify G).Adj u v ↔ u ≠ v ∧ G.Adj u v := by
  simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop,
    exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, ← ne_eq]
  rw [and_comm, and_congr_right_iff]
  exact fun hne ↦ exists_congr fun e ↦ and_iff_right_iff_imp.mpr (Inc₂.edge_mem ·)

instance : IsSimple (Simplify G) where
  loopless x := by
    simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop,
      exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, not_true_eq_false, and_false,
      not_false_eq_true]
  no_multi_edges e f he hf h := by
    simpa only [Simplify, mem_setOf_eq, oftoSym2_tosym2] using h

end Graph
