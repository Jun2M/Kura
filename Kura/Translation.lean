import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Kura.Defs


open edge Graph
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E) (e : E) (u v w : V)

def SimpleGraph.toGraph (G : SimpleGraph V) :
Graph V {s : Sym2 V // Sym2.lift ⟨G.Adj, (fun _ _ => eq_iff_iff.mpr ⟨(G.symm ·), (G.symm ·)⟩)⟩ s} where
  inc := λ e => undir e

namespace Graph

def toEdgeMultiset [Fintype E] : Multiset (edge V) :=
  (@Fintype.elems E _ : Finset E)
  |>.val
  |>.map G.inc

unsafe instance [Repr V] [Fintype E] : Repr (Graph V E) where
  reprPrec G _ := "Graph " ++ repr G.toEdgeMultiset

def Complete (V : Type*) [DecidableEq V] : Graph V {u : Sym2 V // ¬ u.IsDiag} where
  inc e := undir e.val
#eval Complete (Fin 5)

def Cycle (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)
#eval Cycle 5

def Path (n : ℕ+) : Graph (Fin n) (Fin (n-1)) where
  inc e := undir s(e, e+1)

def BipComplete (n₁ n₂ : ℕ+) : Graph (Fin n₁ ⊕ Fin n₂) (Fin n₁ × Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval BipComplete 3 4

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


-- theorem toSimpleGraph_toGraph [simple G] : G.toSimpleGraph.toGraph = G := by
--   ext e
--   cases e with s
--   simp [toSimpleGraph, toGraph]
--   apply Sym2.eq_swap


end Graph
