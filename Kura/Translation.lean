import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Kura.Defs


open edge Graph
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E) (e : E) (u v w : V)


def SimpleGraph.toGraph (G : SimpleGraph V) :
Graph V {s : Sym2 V // Sym2.lift ⟨G.Adj, (fun _ _ => eq_iff_iff.mpr ⟨(G.symm ·), (G.symm ·)⟩)⟩ s} where
  inc := λ e => undir e

namespace Graph

def toSimpleGraph [simple G] : SimpleGraph V where
  Adj := λ v w ↦ ∃ e, G.inc e = undir s(v, w)
  symm := by
    intro v w h
    convert h using 4
    apply Sym2.eq_swap
  loopless := by
    intro v ⟨e, h⟩
    have h' : ¬ G.isLoop e := loopless.no_loops e
    simp [h] at h'


theorem toSimpleGraph_toGraph [simple G] : G.toSimpleGraph.toGraph = G := by
  ext e
  cases e with s
  simp [toSimpleGraph, toGraph]
  apply Sym2.eq_swap

end Graph
