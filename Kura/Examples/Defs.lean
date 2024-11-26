import Kura.Graph.Undirected
import Kura.Dep.List
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Kura.Dep.Toss
import Kura.Graph.Bipartite
import Kura.Dep.Fin
import Mathlib.Data.Sym.Card


namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) (e : E) (u v w : V)


def EdgelessGraph (n : ℕ): Graph (Fin n) Empty where
  inc e := e.elim
#eval! EdgelessGraph 5

instance instEdgelessGraphSimple (n : ℕ) : Simple (EdgelessGraph n) where
  all_full e := e.elim
  no_loops e := e.elim
  edge_symm e := e.elim
  inc_inj e := e.elim




-- def CompleteGraph (n : ℕ) : Graph (Fin n) (Fin (n.choose 2)) where
--   inc e := undir (List.finRange n |>.sym2.filter (¬·.IsDiag) |>.get (e.cast (by rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange])))
-- #eval! CompleteGraph 4
def CompleteGraph (n : ℕ) : Graph (Fin n) {e : Sym2 (Fin n) // ¬ e.IsDiag} where
  inc e := undir e

-- instance instCompleteGraphSimple (n : ℕ) : Simple (CompleteGraph n) where
--   all_full e := by simp only [isFull, edge.isFull, CompleteGraph, List.get_eq_getElem, decide_not]
--   no_loops e := by
--     simp only [isLoop, edge.isLoop, CompleteGraph, List.get_eq_getElem, decide_not,
--       decide_eq_true_eq]
--     have := @List.getElem_filter _ (List.finRange n |>.sym2) (¬·.IsDiag) e.val ?_
--     simpa using this
--     rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
--     exact e.prop
--   edge_symm e := by
--     simp only [isUndir, edge.isUndir, CompleteGraph, List.get_eq_getElem, decide_not]
--   inc_inj e₁ e₂ h := by
--     simp only [CompleteGraph, List.get_eq_getElem, undir.injEq, e₁.prop] at h
--     ext
--     refine List.getElem_inj ?_ ?_ ?_ h
--     rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
--     exact e₁.prop
--     rw [List.sym2_notDiag_length (List.nodup_finRange n), List.length_finRange]
--     exact e₂.prop
--     refine (List.nodup_finRange n).sym2.filter _
instance instCompleteGraphSimple (n : ℕ) : Simple (CompleteGraph n) where
  all_full _ := by simp only [isFull, edge.isFull, CompleteGraph]
  no_loops e := by simp only [isLoop, edge.isLoop, CompleteGraph, e.prop, not_false_eq_true]
  edge_symm _ := by simp only [isUndir, edge.isUndir, CompleteGraph]
  inc_inj e₁ e₂ h := by
    simp only [CompleteGraph, undir.injEq] at h
    exact Subtype.eq h

@[simp]
lemma CompleteGraph_edges_eq (n : ℕ) : (CompleteGraph n).Edges = {e : Sym2 (Fin n) // ¬ e.IsDiag} :=
  rfl

instance instCompleteGraphFintypeE (n : ℕ) : Fintype (CompleteGraph n).Edges :=
  sorry

@[simp 120]
lemma CompleteGraph_edges_card (n : ℕ) : Fintype.card (CompleteGraph n).Edges = n.choose 2 := by
  simp only [CompleteGraph_edges_eq]
  convert Sym2.card_subtype_not_diag
  exact (Fintype.card_fin n).symm
  infer_instance


def TourGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instTourGraphUndirected (n : ℕ+) : Undirected (TourGraph n) where
  edge_symm _ := by simp [TourGraph]
  all_full _ := by simp only [isFull, edge.isFull, TourGraph]


def CycleGraph (n : ℕ) (hn : 1 < n) : Graph (Fin n) (Fin n) := TourGraph ⟨n, by omega⟩
#eval! CycleGraph 5 (by norm_num)

instance instCycleGraphUndir (n : ℕ) (hn : 1 < n) : Undirected (CycleGraph n hn) where
  all_full e := (instTourGraphUndirected ⟨n, by omega⟩).all_full e
  edge_symm e := (instTourGraphUndirected ⟨n, by omega⟩).edge_symm e

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

def PathGraph (n : ℕ) : Graph (Fin (n+1)) (Fin n) where
  inc e := undir s(e, e+1)

lemma PathGraph.adj_iff {n : ℕ} {u v : Fin (n+1)} (huv : u < v):
    (PathGraph n).adj u v ↔ u.val +1 = v.val := by
  constructor <;> intro h
  · obtain ⟨e, he⟩ := h
    unfold PathGraph canGo at he
    simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, canGo_iff_eq_of_undir, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Fin.castSucc_inj, Prod.swap_prod_mk] at he
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he
    · exact rfl
    · absurd huv; clear huv
      simp only [not_lt]
      exact Fin.castSucc_le_succ e
  · unfold PathGraph adj canGo
    use ⟨u.val, sorry⟩
    simp only [Fin.cast_val_eq_self, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      true_and, Prod.swap_prod_mk, add_right_eq_self, Fin.one_eq_zero_iff, add_left_eq_self]
    exact Or.inl sorry

instance instPathGraphSimple (n : ℕ) : Simple (PathGraph n) where
  edge_symm _ := by simp [PathGraph]
  all_full _ := by simp only [isFull, edge.isFull, PathGraph]
  no_loops e := by
    simp only [isLoop, PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, undir_isLoop_iff']
    exact (Fin.succ_ne_castSucc e).symm
  inc_inj e₁ e₂ h := by
    simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, undir.injEq, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Fin.castSucc_inj, Fin.succ_inj, and_self, Prod.swap_prod_mk] at h
    obtain (⟨rfl, rfl⟩ | ⟨h1, h2⟩) := h
    · rfl
    · apply_fun Fin.val at h1 h2 ⊢
      simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
      omega
      exact Fin.val_injective

def CompleteBipGraph (n₁ n₂ : ℕ+) : Graph (Fin n₁ ⊕ₗ Fin n₂) (Fin n₁ ×ₗ Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval CompleteBipGraph 3 4

instance instCompleteBipGraphSimple (n₁ n₂ : ℕ+) : Simple (CompleteBipGraph n₁ n₂) where
  all_full _e := by simp only [isFull, edge.isFull, CompleteBipGraph]
  no_loops e := by simp only [isLoop, edge.isLoop, CompleteBipGraph, Sym2.mk_isDiag_iff]; simp only [reduceCtorEq,
    not_false_eq_true]
  edge_symm _e := by simp only [isUndir, edge.isUndir, CompleteBipGraph]
  inc_inj e₁ e₂ h := by
    simp only [CompleteBipGraph, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, reduceCtorEq, and_self, or_false] at h
    rw [Sum.inl.inj_iff, Sum.inr.inj_iff] at h
    exact Prod.ext_iff.mpr h


instance instCompleteBipGraphBip (n₁ n₂ : ℕ+) : Bipartite (CompleteBipGraph n₁ n₂) where
  L := Sum.inl '' Set.univ
  distinguishes e := by
    simp only [Distinguish, CompleteBipGraph, Set.image_univ, Set.mem_range,
      Sym2.distinguish_pair_iff, exists_apply_eq_apply, reduceCtorEq, exists_const, ne_eq,
      eq_iff_iff, iff_false, not_true_eq_false, not_false_eq_true]
