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

def EdgelessGraph_Emb (fᵥ : W ↪ V) : EdgelessGraph W ⊆ᴳ G where
  fᵥ := fᵥ
  fₑ := Empty.elim
  inc := (Empty.elim ·)
  fᵥinj := fᵥ.injective
  fₑinj := (Empty.elim ·)

@[simp]
lemma EdgelessGraph_Emb_fᵥ {fᵥ : W ↪ V} : (EdgelessGraph_Emb G fᵥ).fᵥ = fᵥ := rfl

@[simp]
lemma EdgelessGraph_Emb_fₑ {fᵥ : W ↪ V} : (EdgelessGraph_Emb G fᵥ).fₑ = Empty.elim :=
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

-- @[simp]
-- lemma CompleteGraph_edges_eq (n : ℕ) : (CompleteGraph n).Edges = {e : Sym2 (Fin n) // ¬ e.IsDiag} :=
--   rfl

-- instance instCompleteGraphFintypeE (n : ℕ) : Fintype (CompleteGraph n).Edges := by
--   simp only [CompleteGraph_edges_eq]
--   infer_instance

-- @[simp 120]
-- lemma CompleteGraph_edges_card (n : ℕ) : Fintype.card (CompleteGraph n).Edges = n.choose 2 := by
--   simp only [CompleteGraph_edges_eq]
--   convert Sym2.card_subtype_not_diag
--   exact (Fintype.card_fin n).symm


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

lemma PathGraph_get {n : ℕ} (e : Fin n) : (PathGraph n).get e = s(e.castSucc, e.succ) := by
  unfold PathGraph
  simp only [get, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, undir.injEq, Classical.choose_eq']

def PathGraph_Emb_Pathgraph {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph n).Emb (PathGraph m) where
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
lemma PathGraph_Emb_Pathgraph_fᵥapply {n m k : ℕ} (hnm : n + k ≤ m) (v : Fin (n+1)) :
    (PathGraph_Emb_Pathgraph hnm).fᵥ v = (v.addNatEmb k).castLE (by omega) := by rfl

@[simp]
lemma PathGraph_Emb_Pathgraph_fₑapply {n m k : ℕ} (hnm : n + k ≤ m) (e : Fin n) :
    (PathGraph_Emb_Pathgraph hnm).fₑ e = (e.addNatEmb k).castLE (by omega) := by rfl

@[simp]
lemma PathGraph_Emb_Pathgraph_start {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph_Emb_Pathgraph hnm).fᵥ 0 = k := by
  simp only [PathGraph_Emb_Pathgraph_fᵥapply, Fin.addNatEmb_apply]
  ext
  simp only [Fin.coe_castLE, Fin.coe_addNat, Fin.val_zero, zero_add, Fin.val_natCast]
  refine (Nat.mod_eq_of_lt ?_).symm
  omega

@[simp]
lemma PathGraph_Emb_Pathgraph_end {n m k : ℕ} (hnm : n + k ≤ m) :
    (PathGraph_Emb_Pathgraph hnm).fᵥ n = ↑(n + k) := by
  simp only [PathGraph_Emb_Pathgraph_fᵥapply, Fin.addNatEmb_apply]
  ext
  rw [Fin.val_natCast]
  simp only [Fin.natCast_eq_last, Fin.addNat_last, Fin.coe_castLE, Fin.coe_cast, Fin.val_last]
  refine (Nat.mod_eq_of_lt ?_).symm
  omega

def PathGraph_glue_PathGraph_eq_PathGraph (n m : ℕ) :
    (EdgelessGraph_Emb (PathGraph n)
      ⟨(fun _ => Fin.last n : Fin 1 → Fin (n+1)), Function.injective_of_subsingleton _⟩).glue
    (EdgelessGraph_Emb (PathGraph m)
      ⟨(fun _ => 0 : Fin 1 → Fin (m+1)), Function.injective_of_subsingleton _⟩) ≃ᴳ
    PathGraph (n + m) where
  fᵥ v := match v with
    | Sum.inl v => v.castLE (by omega)
    | Sum.inr v => v.val.natAdd n
  fₑ e := match e with
    | Sum.inl e => e.castLE (by omega)
    | Sum.inr e => e.val.natAdd n
  inc e := match e with
    | Sum.inl e => by simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ,
      EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk, EdgelessGraph_Emb_fₑ, Emb.glue,
      Set.range_const, Set.mem_singleton_iff, Fin.ext_iff', Fin.val_zero, map_inc, add_inc,
      map_undir, Sym2.map_pair_eq, Fin.castLE_castSucc, Fin.castLE_succ, undir.injEq, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Fin.coe_castSucc, Fin.coe_castLE, and_self, Prod.swap_prod_mk,
      Fin.val_succ, self_eq_add_right, one_ne_zero, add_right_eq_self, or_false]
    | Sum.inr ⟨⟨e, he⟩, hemem⟩ => by
      cases e <;> simp [Emb.glue, PathGraph]
      omega
  fᵥinj v w h := by
    match v, w with
    | Sum.inl ⟨v, hv⟩, Sum.inl ⟨w, hw⟩ =>
      rw [Fin.castLE_inj] at h
      exact congrArg Sum.inl h
    | Sum.inl ⟨v, hv⟩, Sum.inr ⟨⟨w, hw⟩, hwmem⟩ =>
      exfalso
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_Emb_fᵥ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h hwmem
      omega
    | Sum.inr ⟨⟨w, hw⟩, hwmem⟩, Sum.inl ⟨v, hv⟩ =>
      exfalso
      simp [← Fin.val_inj] at h hwmem
      omega
    | Sum.inr v, Sum.inr w =>
      simp only [EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk, Fin.natAdd_inj] at h
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
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_Emb_fₑ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h he₂mem
      omega
    | Sum.inr ⟨⟨e₁, he₁⟩, he₁mem⟩, Sum.inl ⟨e₂, he₂⟩ =>
      exfalso
      simp only [Fin.castLE_mk, Fin.natAdd_mk, ← Fin.val_inj, EdgelessGraph_Emb_fₑ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h he₁mem
      omega
    | Sum.inr v, Sum.inr w =>
      simp only [EdgelessGraph_Emb_fₑ, Function.Embedding.coeFn_mk, Fin.natAdd_inj] at h
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
    simp only [EdgelessGraph_Emb_fₑ, Fin.ext_iff', Sum.exists, Fin.coe_castLE,
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
  simp [EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk, EdgelessGraph_Emb_fₑ,
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

def CycleGraph (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instCycleGraphUndirected (n : ℕ+) : Undirected (CycleGraph n) where
  edge_symm _ := by simp [CycleGraph]
  all_full _ := by simp only [isFull, edge.isFull, CycleGraph]

@[simp]
lemma CycleGraph_get (n : ℕ+) (e : Fin n) : (CycleGraph n).get e = s(e, e+1) := by
  simp only [get, CycleGraph, undir.injEq, Classical.choose_eq']

lemma CycleGraph_isLoop_iff (n : ℕ+) : (CycleGraph n).isLoop 0 ↔ n = 1 := by
  rw [isLoop, CycleGraph, undir_isLoop_iff]
  simp only [zero_add, Sym2.isDiag_iff_proj_eq, Fin.ext_iff', Fin.val_zero, Fin.val_one',
    Nat.Nat.zero_eq_one_mod_iff, PNat.coe_eq_one_iff]

def CycleGraph_Emb_of_isLoop (e : E) (h : G.inc e = undir s(i, i)) : CycleGraph 1 ⊆ᴳ G where
  fᵥ := fun _ => i
  fₑ := fun _ => e
  inc e := by
    simp only [h, PNat.val_ofNat, CycleGraph, Fin.isValue, add_zero, map_undir, Sym2.map_pair_eq]
  fᵥinj _ _ _ := Subsingleton.elim _ _ (h := Fin.subsingleton_one)
  fₑinj _ _ _ := Subsingleton.elim _ _ (h := Fin.subsingleton_one)

def CycleGraph_Emb_of_parallel {e f : E} (henef : e ≠ f) (u v : V) (hunev : u ≠ v)
    (h : G.inc e = G.inc f) (huv : G.inc e = undir s(u, v)) : CycleGraph 2 ⊆ᴳ G where
  fᵥ i := if i = 0 then u else v
  fₑ i := if i = 0 then e else f
  inc i := by
    fin_cases i <;> simp [PNat.val_ofNat, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, ←
      h, huv, Fin.ext_iff', Fin.val_zero, CycleGraph, Fin.reduceAdd, map_undir, Sym2.map_pair_eq,
      Fin.val_one, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_true]
  fᵥinj i j _ := by fin_cases i <;> fin_cases j <;> simp_all
  fₑinj i j _ := by fin_cases i <;> fin_cases j <;> simp_all

def CycleGraph.rotate (n : ℕ+) (k : Fin n) : CycleGraph n ≃ᴳ CycleGraph n where
  fᵥ v := v + k
  fₑ e := e + k
  inc e := by simp only [CycleGraph, map_undir, Sym2.map_pair_eq, add_right_comm]
  fᵥinj := add_left_injective k
  fₑinj := add_left_injective k
  fᵥsurj := add_right_surjective k
  fₑsurj := add_right_surjective k

@[simp]
lemma CycleGraph_rotate_fᵥ (n : ℕ+) (k : Fin n) : (CycleGraph.rotate n k).fᵥ = (· + k) := rfl

@[simp]
lemma CycleGraph_rotate_fₑ (n : ℕ+) (k : Fin n) : (CycleGraph.rotate n k).fₑ = (· + k) := rfl

@[simp]
lemma CycleGraph_rotate_symm_fᵥ (n : ℕ+) (k : Fin n) : (CycleGraph.rotate n k).symm.fᵥ = (· - k) := by
  ext1 v
  apply_fun (CycleGraph.rotate n k).fᵥ using (CycleGraph.rotate n k).fᵥinj
  simp only [Isom.fᵥ_symm_fᵥ, CycleGraph_rotate_fᵥ, sub_add_cancel]

@[simp]
lemma CycleGraph_rotate_symm_fₑ (n : ℕ+) (k : Fin n) : (CycleGraph.rotate n k).symm.fₑ = (· - k) := by
  ext1 e
  apply_fun (CycleGraph.rotate n k).fₑ using (CycleGraph.rotate n k).fₑinj
  simp only [Isom.fₑ_symm_fₑ, CycleGraph_rotate_fₑ, sub_add_cancel]

def CycleGraph.toPathGraph {n : ℕ} {m : ℕ+} (hnm : m = n + 1) :
    (CycleGraph m).Es {-1}ᶜ ≃ᴳ PathGraph n where
  fᵥ := Fin.cast hnm
  fₑ := Fin.singleton_comple_equiv_pred hnm
  inc e := by simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ,
    Fin.singleton_comple_equiv_pred, Fin.coe_castSucc, Equiv.coe_fn_mk, Fin.castSucc_castPred,
    Fin.castPred_succ, Es, Ep, CycleGraph, map_undir, Sym2.map_pair_eq, Fin.cast_add, undir.injEq,
    Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, add_right_inj, Fin.ext_iff', Fin.val_one', Fin.coe_cast,
    hnm, and_self, Prod.swap_prod_mk, self_eq_add_right, Fin.val_zero, Nat.one_mod_eq_zero_iff,
    add_left_eq_self, add_right_eq_self, true_or]
  fᵥinj := Fin.cast_injective hnm
  fₑinj := (Fin.singleton_comple_equiv_pred hnm).injective
  fᵥsurj := Fin.cast_surjective hnm
  fₑsurj := (Fin.singleton_comple_equiv_pred hnm).surjective

@[simp]
lemma CycleGraph_toPathGraph_fᵥ (n : ℕ) {m : ℕ+} (hm : m = n + 1) :
    (CycleGraph.toPathGraph hm).fᵥ = Fin.cast hm := rfl

@[simp]
lemma CycleGraph_toPathGraph_fₑ (n : ℕ) {m : ℕ+} (hm : m = n + 1) :
    (CycleGraph.toPathGraph hm).fₑ = Fin.singleton_comple_equiv_pred hm := rfl

@[simp]
lemma CycleGraph_toPathGraph_symm_fᵥ (n : ℕ) {m : ℕ+} (hm : m = n + 1) :
    (CycleGraph.toPathGraph hm).symm.fᵥ = Fin.cast hm.symm := by
  ext1 v
  apply_fun (CycleGraph.toPathGraph hm).fᵥ using (CycleGraph.toPathGraph hm).fᵥinj
  simp only [Isom.fᵥ_symm_fᵥ, CycleGraph_toPathGraph_fᵥ, Fin.cast_trans, Fin.cast_eq_self]

@[simp]
lemma CycleGraph_toPathGraph_symm_fₑ (n : ℕ) {m : ℕ+} (hm : m = n + 1) :
    (CycleGraph.toPathGraph hm).symm.fₑ = fun e ↦ ⟨e.castSucc, by simp only [Fin.coe_castSucc,
      Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff', Fin.val_natCast, hm,
      Nat.mod_eq_of_lt (Nat.lt_add_right 1 e.prop), Fin.coe_neg_one', add_tsub_cancel_right]; omega⟩ := by
  ext1 e
  apply_fun (CycleGraph.toPathGraph hm).fₑ using (CycleGraph.toPathGraph hm).fₑinj
  simp only [Isom.fₑ_symm_fₑ, Fin.coe_castSucc, CycleGraph_toPathGraph_fₑ,
    Fin.singleton_comple_equiv_pred, Equiv.coe_fn_mk, Fin.ext_iff', Fin.coe_castPred, Fin.coe_cast,
    Fin.val_natCast, hm, Nat.mod_eq_of_lt (Nat.lt_add_right 1 e.prop)]

def CycleGraph_Es_singleton_eq_PathGraph {n : ℕ} {m : ℕ+} (hm : m = n + 1) (i : Fin m) :
    (CycleGraph m).Es {i}ᶜ ≃ᴳ PathGraph n := by
  refine CycleGraph.rotate m (-i - 1) |>.Es_Es ?_ |>.trans (CycleGraph.toPathGraph hm)
  simp only [CycleGraph_rotate_fₑ, Set.image_add_right, neg_sub, sub_neg_eq_add, Set.preimage_compl,
    Set.preimage_add_right_singleton, neg_add_rev, add_neg_cancel_left]

-- def CycleGraph_Es_singleton_eq_PathGraph (n : ℕ) {m : ℕ+} (hm : m = n + 1) (i : Fin m) :
--     (CycleGraph m).Es {i}ᶜ ≃ᴳ PathGraph n where
--   fᵥ := Fin.cast hm - i - 1
--   fₑ e := ⟨(e.val - i - 1).val, lt_of_le_of_ne (by
--     have := (e.val - i - 1).prop
--     omega) (by
--     have : n = m - 1 := by omega
--     subst n
--     rw [← Fin.coe_neg_one', Fin.val_injective.ne_iff, ← zero_sub, ← sub_self i,
--       sub_left_injective.ne_iff, sub_left_injective.ne_iff]
--     exact e.prop)⟩
--   inc e := by
--     simp [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.castSucc_mk, Fin.succ_mk,
--       Pi.natCast_def, CycleGraph, Es_inc, map_undir, Pi.sub_apply, Pi.one_apply, Sym2.map_pair_eq,
--       undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Fin.ext_iff', Prod.swap_prod_mk]
--     left
--     constructor
--     · simp? [Fin.sub_def, hm, Nat.le_add_left]

--       rw [Fin.val_injective.eq_iff, sub_left_injective.eq_iff, sub_left_injective.eq_iff]

--       sorry
--     ·
--       sorry
--   fᵥinj _ _ a := by
--     ext
--     simpa [Fin.castLE_inj] using a
--   fₑinj e1 e2 h := by
--     ext1
--     simp only [Fin.ext_iff'] at h
--     rwa [Fin.val_injective.eq_iff, sub_left_injective.eq_iff, sub_left_injective.eq_iff] at h
--   fᵥsurj x := by
--     simp only [Pi.natCast_def, Pi.sub_apply, Pi.one_apply]
--     use x.cast hm.symm + 1 + i
--     simp [Fin.ext_iff']
--     rw [Fin.cast_eq_val_cast hm, Fin.cast_eq_val_cast hm, add_sub_cancel_right, ← Fin.ext_iff']
--     convert add_sub_cancel_right x 1
--     simp only [Fin.val_one', hm, Fin.ext_iff', Fin.val_natCast, dvd_refl, Nat.mod_mod_of_dvd]
--   fₑsurj e := by
--     simp
--     use e + 1 + i
--     constructor
--     · rw [Fin.val_injective.eq_iff, add_toss_eq, sub_self, add_toss_eq, zero_sub,
--         ← Fin.val_injective.eq_iff]
--       simp only [Fin.val_natCast, hm, Fin.coe_neg_one', add_tsub_cancel_right]
--       rw [Nat.mod_eq_of_lt (by omega)]
--       omega
--     · rw [add_sub_cancel_right, add_sub_cancel_right]
--       have := e.prop
--       simp only [Fin.val_natCast, hm, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, gt_iff_lt]
--       omega

def CycleGraph_Isom_PathGraph_addUndirEdge (n : ℕ) {m : ℕ+} (hm : m = n.succPNat) :
    (CycleGraph m).Isom (PathGraph n |>.addUndirEdge s(0, Fin.last _)) where
  fᵥ := Fin.cast (by subst m; rfl)
  fₑ e :=
    if h : e = Fin.last n
    then Sum.inr ()
    else Sum.inl (e.castPred (by subst m; simp_all))
  inc e := by
    subst m
    by_cases h : e = Fin.last n
    · simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, h, Fin.val_last, Fin.natCast_eq_last,
      ↓reduceDIte, addUndirEdge_inc_inr, CycleGraph, Fin.last_add_one, map_undir, Fin.cast_eq_self,
      Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Fin.ext_iff',
      Fin.val_zero, Prod.swap_prod_mk, or_true]
    · simp only [addUndirEdge, PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ,
      Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.val_last, Fin.natCast_eq_last, h, ↓reduceDIte,
      Fin.cast_val_eq_self, Fin.castSucc_castPred, Fin.castPred_succ, Fin.cast_refl, CycleGraph,
      map_undir, id_eq, Sym2.map_pair_eq]
  fᵥinj _ _ a := by simpa using a
  fₑinj e1 e2 h := by
    subst m
    by_cases he1 : e1 = Fin.last n <;> by_cases he2 : e2 = Fin.last n <;>
    simp_all [Nat.succPNat_coe, Nat.succ_eq_add_one, dite_true, dite_false, Sum.inl_injective.eq_iff]
  fᵥsurj _ := by subst m; simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.cast_eq_self,
    Fin.ext_iff', exists_apply_eq_apply]
  fₑsurj e := by
    subst m
    simp
    match e with
    | Sum.inl e =>
      use e
      simp [e.prop.ne]
    | Sum.inr () =>
      use Fin.last _
      simp

-- def CycleGraph_Isom_PathGraph_addUndirEdge' (n : ℕ) :
--     (CycleGraph n.succPNat).Isom (PathGraph n |>.addUndirEdge s(0, Fin.last _)) where
--   fᵥ v := v
--   fₑ e :=
--     if h : e = Fin.last _
--     then Sum.inr ()
--     else Sum.inl (e.castPred h)
--   inc e := by
--     by_cases h : e = Fin.last _
--     · simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, h, ↓reduceDIte, addUndirEdge_inc_inr,
--       CycleGraph, Fin.last_add_one, map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff',
--       Prod.mk.injEq, Fin.zero_eq_last_iff, Fin.last_eq_zero_iff, and_self, Prod.swap_prod_mk,
--       or_true]
--     · simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Nat.succPNat_coe,
--       Nat.succ_eq_add_one, h, ↓reduceDIte, addUndirEdge_inc_inl, Fin.castSucc_castPred, CycleGraph,
--       map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and,
--       Prod.swap_prod_mk, self_eq_add_right, Fin.one_eq_zero_iff, add_left_eq_self]
--       left
--       exact Fin.castPred_succ e h
--   fᵥinj _ _ a := a
--   fₑinj e1 e2 h := by
--     by_cases he1 : e1 = Fin.last _ <;> by_cases he2 : e2 = Fin.last _ <;>
--     simp_all [Nat.succPNat_coe, Nat.succ_eq_add_one, dite_true, dite_false, Sum.inl_injective.eq_iff]
--   fᵥsurj _ := by simp only [exists_eq]
--   fₑsurj e :=
--     match e with
--     | Sum.inl e => by
--       use e
--       simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.castSucc_ne_last,
--         ↓reduceDIte, Fin.castPred_castSucc]
--     | Sum.inr () => by
--       use Fin.last _
--       simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, ↓reduceDIte]

-- def CycleGraph (n : ℕ) (hn : 1 < n) : Graph (Fin n) (Fin n) := CycleGraph' ⟨n, by omega⟩
-- #eval! CycleGraph 5 (by norm_num)

-- instance instCycleGraphUndir (n : ℕ) (hn : 1 < n) : Undirected (CycleGraph n hn) where
--   all_full e := (instCycleGraph'Undirected ⟨n, by omega⟩).all_full e
--   edge_symm e := (instCycleGraph'Undirected ⟨n, by omega⟩).edge_symm e

-- instance instCycleGraphSimple (n : ℕ) (hn : 2 < n) : Simple (CycleGraph n (by omega)) where
-- all_full e := (instCycleGraph'Undirected ⟨n, by omega⟩).all_full e
-- no_loops e := by
--   have : NeZero n := {out := by omega}
--   simp only [isLoop, CycleGraph, CycleGraph', id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
--     Nat.cast_ofNat, Int.reduceAdd, PNat.mk_coe, undir_isLoop_iff', self_eq_add_right,
--     Fin.one_eq_zero_iff, ne_eq]
--   omega
-- edge_symm e := (instCycleGraph'Undirected ⟨n, by omega⟩).edge_symm e
-- inc_inj e₁ e₂ h := by
--   simp only [CycleGraph, CycleGraph', id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat,
--     Int.reduceAdd, PNat.mk_coe, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, add_left_inj,
--     and_self, Prod.swap_prod_mk] at h
--   rcases h with (rfl | ⟨h₁,h₂⟩)
--   · rfl
--   · have : Fact (2 < n) := ⟨hn⟩
--     have : NeZero n := {out := by omega}
--     subst h₂
--     rw [← sub_toss_eq, sub_eq_add_neg, add_left_cancel_iff] at h₁
--     absurd h₁
--     exact CharP.neg_one_ne_one (Fin n) n

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
