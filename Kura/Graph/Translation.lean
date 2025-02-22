import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Kura.Graph.Undirected
import Kura.Dep.Rel


open edge Graph
variable {V W E F : Type*}

@[simp]
def SimpleGraph.toGraph (G : SimpleGraph V) :
Graph V {s : Sym2 V // Sym2.lift ⟨G.Adj, (fun _ _ => eq_iff_iff.mpr ⟨(G.symm ·), (G.symm ·)⟩)⟩ s} where
  inc := λ e => undir e

instance SimpleGraph.toGraphSimple (G : SimpleGraph V) : Simple (G.toGraph) where
  all_full e := by
    simp only [Graph.isFull, toGraph, undir_isFull]
  no_loops e := by
    rcases e with ⟨s, h⟩
    simp only [Graph.isLoop, toGraph, undir_isLoop_iff]
    rw [Sym2.eq_mk_out s, Sym2.mk_isDiag_iff]
    rw [Sym2.eq_mk_out s, Sym2.lift_mk ⟨G.Adj, _⟩ s.out.1 s.out.2] at h
    exact G.loopless.ne_of_rel h
  edge_symm e := by
    rcases e with ⟨s, _h⟩
    simp only [Graph.isUndir, toGraph, isUndir_of_undir]
  inc_inj e1 e2 := by
    rcases e1 with ⟨s1, h1⟩
    rcases e2 with ⟨s2, h2⟩
    simp only [toGraph, undir.injEq, Subtype.mk.injEq, imp_self]

@[simp]
lemma SimpleGraph.toGraph_adj [DecidableEq V] (G : SimpleGraph V) (v w : V) :
  G.toGraph.adj v w ↔ G.Adj v w := by
  simp only [adj, Graph.canGo, toGraph, canGo_iff_eq_of_undir, Subtype.exists, exists_prop,
    exists_eq_right, Sym2.lift_mk]

namespace Graph
variable (G : Graph V E) [Simple G]

def toSimpleGraph : SimpleGraph V where
  Adj := λ v w ↦ ∃ e, G.inc e = undir s(v, w)
  symm := by
    intro v w h
    convert h using 4
    apply Sym2.eq_swap
  loopless := by
    intro v ⟨e, h⟩
    have h' : ¬ G.isLoop e := loopless.no_loops e
    simp only [isLoop, h, undir_isLoop_iff, Sym2.isDiag_iff_proj_eq, not_true_eq_false] at h'

@[simp]
lemma toSimpleGraph_Adj [DecidableEq V] (v w : V) : G.toSimpleGraph.Adj v w ↔ G.adj v w := by
  simp only [toSimpleGraph, inc_eq_undir_v12, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, adj, canGo, canGo_iff_eq_of_undir]

theorem toGraph_toSimpleGraph (G : SimpleGraph V) : G.toGraph.toSimpleGraph = G := by
  ext v e
  simp only [toSimpleGraph, SimpleGraph.toGraph, undir.injEq, Subtype.exists, exists_prop',
    nonempty_prop, exists_eq_right, Sym2.lift_mk]

def toSimpleGraph_toGraph [DecidableEq V] : G ≃ᴳ G.toSimpleGraph.toGraph where
  fᵥ := by exact id
  fₑ e := by
    let s := G.get e
    use s
    generalize h : s = a
    induction' a with v w
    rw [G.get_eq_iff_canGo] at h
    simp only [Sym2.lift_mk, toSimpleGraph_Adj]
    use e
  inc e := by simp only [SimpleGraph.toGraph, inc_eq_get, map_undir, id_eq, Sym2.map_id']
  fᵥinj v w h := h
  fₑinj e f h := by simpa only [Subtype.mk.injEq, get_inj_iff] using h
  fᵥsurj v := by simp only [id_eq, exists_eq]
  fₑsurj e := by
    obtain ⟨s, hs⟩ := e
    induction' s with v w
    simp only [Sym2.lift_mk, toSimpleGraph_Adj] at hs
    obtain ⟨e, he⟩ := hs
    use e
    simpa only [Subtype.mk.injEq, get_eq_iff_canGo]


end Graph
