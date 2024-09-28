import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Kura.Defs
import Kura.Dep.List


open edge Graph
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)

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

-- def CompleteGraph (V : Type*) [LinearOrder V] : Graph V {u : Sym2 V // ¬ u.IsDiag} where
--   inc e := undir e.val
def CompleteGraph (n : ℕ) : Graph (Fin n) (Fin (n.choose 2)) where
  inc e := undir (List.finRange n |>.sym2.filter (¬·.IsDiag) |>.get (e.cast (by rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange])))
#eval! CompleteGraph 4

instance instCompleteGraphSimple (n : ℕ) : Simple (CompleteGraph n) where
  all_full e := by simp only [isFull, edge.isFull, CompleteGraph, List.get_eq_getElem, decide_not]
  no_loops e := by
    simp only [isLoop, edge.isLoop, CompleteGraph, List.get_eq_getElem, decide_not,
      decide_eq_true_eq]
    have := @List.getElem_filter _ (List.finRange n |>.sym2) (¬·.IsDiag) e.val ?_
    simpa using this
    rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
    exact e.prop
  edge_symm e := by
    simp only [isUndir, edge.isUndir, CompleteGraph, List.get_eq_getElem, decide_not]
  inc_inj e₁ e₂ h := by
    simp only [CompleteGraph, List.get_eq_getElem, undir.injEq, e₁.prop] at h
    ext
    refine List.getElem_inj ?_ ?_ ?_ h
    rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
    exact e₁.prop
    rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
    exact e₂.prop
    refine (List.nodup_finRange n).sym2.filter _

def CycleGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)
#eval CycleGraph 5

def PathGraph (n : ℕ+) : Graph (Fin n) (Fin (n-1)) where
  inc e := undir s(e, e+1)

def CompleteBipGraph (n₁ n₂ : ℕ+) : Graph (Lex $ Fin n₁ ⊕ Fin n₂) (Lex $ Fin n₁ × Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval CompleteBipGraph 3 4

def toSimpleGraph [Simple G] : SimpleGraph V where
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
