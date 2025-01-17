import Kura.Graph.Undirected
import Kura.Dep.List
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Kura.Dep.Toss
import Kura.Graph.Bipartite
import Kura.Dep.Fin
import Mathlib.Data.Sym.Card
import Kura.Graph.Add


namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) (e : E) (u v w : V)


def EdgelessGraph (W) : Graph W Empty where
  inc e := e.elim

instance instEdgelessGraphSimple : Simple (EdgelessGraph V) where
  all_full e := e.elim
  no_loops e := e.elim
  edge_symm e := e.elim
  inc_inj e := e.elim

def EdgelessGraph_SubgraphOf (fᵥ : W ↪ V) : EdgelessGraph W ⊆ᴳ G where
  fᵥ := fᵥ
  fₑ := Empty.elim
  inc := (Empty.elim ·)
  fᵥinj := fᵥ.injective
  fₑinj := (Empty.elim ·)

@[simp]
lemma EdgelessGraph_SubgraphOf_fᵥ {fᵥ : W ↪ V} : (EdgelessGraph_SubgraphOf G fᵥ).fᵥ = fᵥ := rfl

@[simp]
lemma EdgelessGraph_SubgraphOf_fₑ {fᵥ : W ↪ V} : (EdgelessGraph_SubgraphOf G fᵥ).fₑ = Empty.elim :=
  rfl

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

instance instCompleteGraphFintypeE (n : ℕ) : Fintype (CompleteGraph n).Edges := by
  simp only [CompleteGraph_edges_eq]
  infer_instance

@[simp 120]
lemma CompleteGraph_edges_card (n : ℕ) : Fintype.card (CompleteGraph n).Edges = n.choose 2 := by
  simp only [CompleteGraph_edges_eq]
  convert Sym2.card_subtype_not_diag
  exact (Fintype.card_fin n).symm


def PathGraph (n : ℕ) : Graph (Fin (n+1)) (Fin n) where
  inc e := undir s(e, e+1)

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

lemma PathGraph.canGo' {n : ℕ} (e : Fin n) :
    (PathGraph n).canGo e.castSucc e e.succ := by
  unfold PathGraph canGo
  simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, undir_canGo]

@[simp]
lemma PathGraph.canGo_iff {n : ℕ} {u v : Fin (n+1)} {e : Fin n} :
    (PathGraph n).canGo u e v ↔ s(e.castSucc, e.succ) = s(u, v) := by
  unfold PathGraph canGo
  simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, edge.canGo_iff_eq_of_undir, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]

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
    use ⟨u.val, Fin.val_lt_last <| Fin.ne_last_of_lt huv⟩
    simp only [Fin.cast_val_eq_self, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      true_and, Prod.swap_prod_mk, add_right_eq_self, Fin.one_eq_zero_iff, add_left_eq_self]
    left
    apply_fun Fin.val using Fin.val_injective
    rw [← h, Fin.val_add_one]
    simp only [ite_eq_right_iff, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
      and_false, imp_false]
    exact Fin.ne_last_of_lt huv

def PathGraph_SubgraphOf_Pathgraph {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph n).SubgraphOf (PathGraph m) where
  fᵥ v := (v.addNatEmb k).castLE (by omega)
  fₑ e := (e.addNatEmb k).castLE (by omega)
  inc e := by
    simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, map_undir, Sym2.map_pair_eq,
      undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    refine Or.inl ⟨?_,?_⟩ <;> ext
    · simp only [Fin.addNatEmb_apply, Fin.coe_castSucc, Fin.coe_castLE, Fin.coe_addNat]
    · simp only [Fin.addNatEmb_apply, Fin.val_succ, Fin.coe_castLE, Fin.coe_addNat]
      omega
  fᵥinj _ _ a := by
    simp only [Fin.castLE_inj] at a
    exact Function.Embedding.injective _ a
  fₑinj e₁ e₂ h := by
    simp only [Fin.castLE_inj] at h
    exact Function.Embedding.injective _ h

@[simp]
lemma PathGraph_SubgraphOf_Pathgraph_fᵥapply {n m k : ℕ} (hnm : n + k ≤ m) (v : Fin (n+1)) :
    (PathGraph_SubgraphOf_Pathgraph hnm).fᵥ v = (v.addNatEmb k).castLE (by omega) := by rfl

@[simp]
lemma PathGraph_SubgraphOf_Pathgraph_fₑapply {n m k : ℕ} (hnm : n + k ≤ m) (e : Fin n) :
    (PathGraph_SubgraphOf_Pathgraph hnm).fₑ e = (e.addNatEmb k).castLE (by omega) := by rfl

@[simp]
lemma PathGraph_SubgraphOf_Pathgraph_start {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph_SubgraphOf_Pathgraph hnm).fᵥ 0 = k := by
  simp only [PathGraph_SubgraphOf_Pathgraph_fᵥapply, Fin.addNatEmb_apply]
  ext
  simp only [Fin.coe_castLE, Fin.coe_addNat, Fin.val_zero, zero_add, Fin.val_natCast]
  refine (Nat.mod_eq_of_lt ?_).symm
  omega

@[simp]
lemma PathGraph_SubgraphOf_Pathgraph_end {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph_SubgraphOf_Pathgraph hnm).fᵥ n = ↑(n + k) := by
  simp only [PathGraph_SubgraphOf_Pathgraph_fᵥapply, Fin.addNatEmb_apply]
  ext
  rw [Fin.val_natCast]
  simp only [Fin.natCast_eq_last, Fin.addNat_last, Fin.coe_castLE, Fin.coe_cast, Fin.val_last]
  refine (Nat.mod_eq_of_lt ?_).symm
  omega

def PathGraph_glue_PathGraph_eq_PathGraph (n m : ℕ) :
    (EdgelessGraph_SubgraphOf (PathGraph n)
      ⟨(fun _ => Fin.last n : Fin 1 → Fin (n+1)), Function.injective_of_subsingleton _⟩).glue
    (EdgelessGraph_SubgraphOf (PathGraph m)
      ⟨(fun _ => 0 : Fin 1 → Fin (m+1)), Function.injective_of_subsingleton _⟩) ≃ᴳ
    PathGraph (n + m) where
  fᵥ v := match v with
    | Sum.inl v => v.castLE (by omega)
    | Sum.inr v => v.val.natAdd n
  fₑ e := match e with
    | Sum.inl e => e.castLE (by omega)
    | Sum.inr e => e.val.natAdd n
  inc e := match e with
    | Sum.inl e => by simp [SubgraphOf.glue, PathGraph]
    | Sum.inr ⟨⟨e, he⟩, hemem⟩ => by
      cases e <;> simp [SubgraphOf.glue, PathGraph]
      omega
  fᵥinj v w h := by
    match v, w with
    | Sum.inl ⟨v, hv⟩, Sum.inl ⟨w, hw⟩ =>
      rw [Fin.castLE_inj] at h
      exact congrArg Sum.inl h
    | Sum.inl ⟨v, hv⟩, Sum.inr ⟨⟨w, hw⟩, hwmem⟩ =>
      exfalso
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_SubgraphOf_fᵥ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h hwmem
      omega
    | Sum.inr ⟨⟨w, hw⟩, hwmem⟩, Sum.inl ⟨v, hv⟩ =>
      exfalso
      simp [← Fin.val_inj] at h hwmem
      omega
    | Sum.inr v, Sum.inr w =>
      simp only [EdgelessGraph_SubgraphOf_fᵥ, Function.Embedding.coeFn_mk, Fin.natAdd_inj] at h
      rw [Sum.inr.injEq]
      exact SetCoe.ext h
  fₑinj e₁ e₂ h := by
    save
    match e₁, e₂ with
    | Sum.inl ⟨e₁, he₁⟩, Sum.inl ⟨e₂, he₂⟩ =>
      simp only [Fin.castLE_inj] at h
      exact congrArg Sum.inl h
    | Sum.inl ⟨e₁, he₁⟩, Sum.inr ⟨⟨e₂, he₂⟩, he₂mem⟩ =>
      exfalso
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_SubgraphOf_fₑ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h he₂mem
      omega
    | Sum.inr ⟨⟨e₁, he₁⟩, he₁mem⟩, Sum.inl ⟨e₂, he₂⟩ =>
      exfalso
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_SubgraphOf_fₑ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h he₁mem
      omega
    | Sum.inr v, Sum.inr w =>
      simp only [EdgelessGraph_SubgraphOf_fₑ, Function.Embedding.coeFn_mk, Fin.natAdd_inj] at h
      rw [Sum.inr.injEq]
      exact SetCoe.ext h
  fᵥsurj v := by
    obtain ⟨v, hv⟩ := v
    simp
    by_cases h : v ≤ n
    · left
      use v
      simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      omega
    · right
      use ↑(v - n)
      have : (v - n) % (m + 1) = v - n := by
        rw [Nat.mod_eq_of_lt]
        omega
      refine ⟨?_, ?_⟩
      · simp only [Fin.val_natCast, this]
        omega
      · simp only [Fin.val_natCast, this]
        omega
  fₑsurj e := by
    obtain ⟨e, he⟩ := e
    simp only [EdgelessGraph_SubgraphOf_fₑ, Fin.ext_iff', Sum.exists, Fin.coe_castLE,
      Fin.coe_natAdd, Subtype.exists, Set.mem_compl_iff, Set.mem_range, IsEmpty.exists_iff,
      not_false_eq_true, exists_const]
    by_cases h : e < n
    · left
      use ⟨e, h⟩
    · right
      use ⟨e - n, by omega⟩
      simp only
      omega

@[simp]
lemma PathGraph_glue_PathGraph_eq_PathGraph_fᵥ (n m : ℕ) :
    (PathGraph_glue_PathGraph_eq_PathGraph n m).fᵥ = (fun v => by
    match v with
    | Sum.inl v => exact v.castLE (by omega)
    | Sum.inr v => exact v.val.natAdd n) := rfl

@[simp]
lemma PathGraph_glue_PathGraph_eq_PathGraph_symm_fᵥ (n m : ℕ) :
    (PathGraph_glue_PathGraph_eq_PathGraph n m).symm.fᵥ = (fun x => by
    by_cases h : x.val ≤ n
    · exact Sum.inl x
    · exact Sum.inr ⟨↑((x.cast (by omega : _ = m + 1 + n)).subNat n (by simp_all; omega)), by
      obtain ⟨x, hx⟩ := x
      simp [← Nat.dvd_iff_mod_eq_zero] at h ⊢
      omega⟩) := by
  ext v
  apply_fun (PathGraph_glue_PathGraph_eq_PathGraph n m).fᵥ using (PathGraph_glue_PathGraph_eq_PathGraph n m).fᵥinj
  simp [EdgelessGraph_SubgraphOf_fᵥ, Function.Embedding.coeFn_mk, EdgelessGraph_SubgraphOf_fₑ,
    Isom.fᵥ_symm_fᵥ, PathGraph_glue_PathGraph_eq_PathGraph_fᵥ, Fin.ext_iff']
  split
  · rename_i x y h
    split_ifs at h with hvn
    · simp_all
      rwa [Nat.mod_eq_of_lt (by omega)] at h
  · rename_i x y h
    split_ifs at h with hvn
    · simp at hvn h ⊢
      subst h
      simp
      omega

@[simp]
lemma PathGraph_glue_PathGraph_eq_PathGraph_fₑ (n m : ℕ) :
    (PathGraph_glue_PathGraph_eq_PathGraph n m).fₑ = (fun e => by
    match e with
    | Sum.inl e => exact e.castLE (by omega)
    | Sum.inr e => exact e.val.natAdd n) := rfl

def TourGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instTourGraphUndirected (n : ℕ+) : Undirected (TourGraph n) where
  edge_symm _ := by simp [TourGraph]
  all_full _ := by simp only [isFull, edge.isFull, TourGraph]

def TourGraph_Isom_PathGraph_addUndirEdge (n : ℕ) :
    (TourGraph n.succPNat).Isom (PathGraph n |>.addUndirEdge s(0, Fin.last _)) where
  fᵥ v := v
  fₑ e :=
    if h : e = Fin.last _
    then Sum.inr ()
    else Sum.inl (e.castPred h)
  inc e := by
    by_cases h : e = Fin.last _
    · simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, h, ↓reduceDIte, addUndirEdge_inc_inr,
      TourGraph, Fin.last_add_one, map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Fin.zero_eq_last_iff, Fin.last_eq_zero_iff, and_self, Prod.swap_prod_mk,
      or_true]
    · simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Nat.succPNat_coe,
      Nat.succ_eq_add_one, h, ↓reduceDIte, addUndirEdge_inc_inl, Fin.castSucc_castPred, TourGraph,
      map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and,
      Prod.swap_prod_mk, self_eq_add_right, Fin.one_eq_zero_iff, add_left_eq_self]
      left
      exact Fin.castPred_succ e h
  fᵥinj _ _ a := a
  fₑinj e1 e2 h := by
    by_cases he1 : e1 = Fin.last _ <;> by_cases he2 : e2 = Fin.last _ <;>
    simp_all [Nat.succPNat_coe, Nat.succ_eq_add_one, dite_true, dite_false, Sum.inl_injective.eq_iff]
  fᵥsurj _ := by simp only [exists_eq]
  fₑsurj e :=
    match e with
    | Sum.inl e => by
      use e
      simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.castSucc_ne_last,
        ↓reduceDIte, Fin.castPred_castSucc]
    | Sum.inr () => by
      use Fin.last _
      simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, ↓reduceDIte]

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
