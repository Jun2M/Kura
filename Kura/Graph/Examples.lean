import Kura.Conn.Conn
import Kura.Dep.List
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Kura.Dep.Toss
import Kura.Graph.Bipartite


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)


instance LinearOrderEmpty : LinearOrder Empty where
  le := fun _ _ => True
  le_refl a := a.elim
  le_trans a := a.elim
  le_antisymm a := a.elim
  le_total a := a.elim
  decidableLE a := a.elim
  compare a := a.elim
  decidableEq a := a.elim

def EdgelessGraph (n : ℕ): Graph (Fin n) Empty where
  inc e := e.elim
#eval! EdgelessGraph 5

instance instEdgelessGraphSimple (n : ℕ) : Simple (EdgelessGraph n) where
  all_full e := e.elim
  no_loops e := e.elim
  edge_symm e := e.elim
  inc_inj e := e.elim

instance instEdgelessGraphConnected (n : ℕ) [Fact (n < 2)] : (EdgelessGraph n).connected where
  all_conn u v := by have : n < 2 := Fact.out; interval_cases n <;> rw [Subsingleton.allEq u v] <;>
    apply conn_refl

lemma EdgelessGraph_not_connected (n : ℕ) (hn : 2 ≤ n) : ¬ (EdgelessGraph n).connected := by
  intro h
  obtain ⟨u, v, huv⟩ := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨P, rfl, rfl⟩ := (h.all_conn u v).path
  by_cases hPlen : P.length = 0
  · rw [P.length_zero_iff_eq_nil] at hPlen
    rw [hPlen] at huv
    simp only [Path.nil_start, Path.nil_finish, ne_eq, not_true_eq_false] at huv
  · obtain e := P.edges.head ((Walk.length_ne_zero_iff_edges_ne_nil P.toWalk).mp hPlen)
    exact e.elim


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

instance instCompleteGraphConnected (n : ℕ) : (CompleteGraph n).connected := by
  sorry

def TourGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instTourGraphUndirected (n : ℕ+) : Undirected (TourGraph n) where
  edge_symm _ := by simp [TourGraph]
  all_full _ := by simp only [isFull, edge.isFull, TourGraph]


def CycleGraph (n : ℕ) (hn : 1 < n) : Graph (Fin n) (Fin n) := TourGraph ⟨n, by omega⟩
#eval! CycleGraph 5 (by norm_num)


instance instCycleGraphSimple (n : ℕ) (hn : 2 < n) : Simple (CycleGraph n (by omega)) where
all_full e := (instTourGraphUndirected ⟨n, by omega⟩).all_full e
no_loops e := by
  have : NeZero n := {out := by omega}
  simp only [isLoop, CycleGraph, TourGraph, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
    Nat.cast_ofNat, Int.reduceAdd, PNat.mk_coe, undir_isLoop_iff', self_eq_add_right,
    Fin.one_eq_zero_iff, ne_eq]
  omega
edge_symm e := (instTourGraphUndirected ⟨n, by omega⟩).edge_symm e
inc_inj e₁ e₂ h := by
  simp only [CycleGraph, TourGraph, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat,
    Int.reduceAdd, PNat.mk_coe, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, add_left_inj,
    and_self, Prod.swap_prod_mk] at h
  rcases h with (rfl | ⟨h₁,h₂⟩)
  · rfl
  · have : Fact (2 < n) := ⟨hn⟩
    have : NeZero n := {out := by omega}
    subst h₂
    rw [← sub_toss_eq, sub_eq_add_neg, add_left_cancel_iff] at h₁
    absurd h₁
    exact CharP.neg_one_ne_one (Fin n) n

def PathGraph (n : ℕ+) : Graph (Fin n) (Fin (n-1)) where
  inc e := undir s(e, e+1)


def CompleteBipGraph (n₁ n₂ : ℕ+) : Graph (Fin n₁ ⊕ₗ Fin n₂) (Fin n₁ ×ₗ Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval CompleteBipGraph 3 4

instance instCompleteBipGraphSimple (n₁ n₂ : ℕ+) : Simple (CompleteBipGraph n₁ n₂) where
  all_full _e := by simp only [isFull, edge.isFull, CompleteBipGraph]
  no_loops e := by simp only [isLoop, edge.isLoop, CompleteBipGraph, Sym2.isDiag_iff_inf_eq_sup,
    Sym2.inf_mk, Sym2.sup_mk, inf_eq_sup, reduceCtorEq, decide_False, Bool.false_eq_true,
    not_false_eq_true]
  edge_symm _e := by simp only [isUndir, edge.isUndir, CompleteBipGraph]
  inc_inj e₁ e₂ h := by
    simp only [CompleteBipGraph, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, reduceCtorEq, and_self, or_false] at h
    rw [Sum.inl.inj_iff, Sum.inr.inj_iff] at h
    exact Prod.ext_iff.mpr h

instance instCompleteBipGraphConnected (n₁ n₂ : ℕ+) : (CompleteBipGraph n₁ n₂).connected := by
  sorry

instance instCompleteBipGraphBip (n₁ n₂ : ℕ+) : Bipartite (CompleteBipGraph n₁ n₂) where
  L := sorry
  hLDec := sorry
  distinguishes := sorry
