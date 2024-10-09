import Kura.Graph.Defs
import Kura.Dep.List
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)


def toEdgeMultiset [Fintype E] : Multiset (edge V) :=
  (@Fintype.elems E _ : Finset E)
  |>.val
  |>.map G.inc

unsafe instance [Repr V] [Fintype E] : Repr (Graph V E) where
  reprPrec G _ := "Graph " ++ repr G.toEdgeMultiset

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


def TourGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instTourGraphUndirected (n : ℕ+) : Undirected (TourGraph n) where
  edge_symm _ := by simp [TourGraph]
  all_full _ := by simp only [isFull, edge.isFull, TourGraph]


def CycleGraph (n : ℕ+) (hn : 1 < n) : Graph (Fin n) (Fin n) := TourGraph n
#eval! CycleGraph 5 (by norm_num)

instance instCycleGraphSimple (n : ℕ+) (hn : 2 < n) : Simple (CycleGraph n sorry) where
all_full e := (instTourGraphUndirected ⟨n, PNat.pos n⟩).all_full e
no_loops e := by
  simp only [isLoop, CycleGraph, TourGraph, undir_isLoop_iff, Sym2.isDiag_iff_proj_eq,
    self_eq_add_right, Fin.one_eq_zero_iff, PNat.coe_eq_one_iff]
  sorry
edge_symm e := (instTourGraphUndirected n).edge_symm e
inc_inj e₁ e₂ h := by
  unfold CycleGraph TourGraph at h
  simp only [undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, add_left_inj, and_self,
    Prod.swap_prod_mk] at h
  rcases h with (rfl | ⟨h₁,h₂⟩)
  · rfl
  · rw [← h₂] at h₁
    have h' : e₁.1 = (e₁ +1 +1).1 := sorry

    rw [show e₁ + 1 = e₁.add 1 from rfl] at h'
    rw [show e₁.add 1 + 1 = (e₁.add 1).add 1 from rfl] at h'
    unfold Fin.add at h'
    simp only [Nat.add_mod_mod, Nat.mod_add_mod] at h'
    sorry

    -- want to conclude that since `x = x+2 mod n`, that `n = 2`,
    -- therefore this is not a valid cycle.


def PathGraph (n : ℕ+) : Graph (Fin n) (Fin (n-1)) where
  inc e := undir s(e, e+1)


def CompleteBipGraph (n₁ n₂ : ℕ+) : Graph (Lex $ Fin n₁ ⊕ Fin n₂) (Lex $ Fin n₁ × Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval CompleteBipGraph 3 4
