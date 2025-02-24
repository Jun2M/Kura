import Mathlib.Data.Sym.Card
import Kura.Dep.List
import Kura.Dep.Toss
import Kura.Dep.Fin
import Kura.Graph.Undirected
import Kura.Graph.Bipartite


namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) (e : E) (u v w : V)


/-- `EdgelessGraph` constructs a graph with vertices `W` and no edges.
    This is useful as a base case for graph constructions and for embedding into other graphs.

    ## Implementation notes
    The edge type is explicitly `Empty` to ensure there can be no edges.
    The `inc` function is defined via `Empty.elim` since there are no edges to map.
-/
def EdgelessGraph (W) : Graph W Empty where
  inc e := e.elim

instance instEdgelessGraphSimple : Simple (EdgelessGraph V) where
  all_full e := e.elim
  no_loops e := e.elim
  edge_symm e := e.elim
  inc_inj e := e.elim

lemma EdgelessGraph.adj [DecidableEq W] {u v : W} : ¬ (EdgelessGraph W).adj u v := by
  simp only [Graph.adj, IsEmpty.exists_iff, not_false_eq_true]

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


/-- `CompleteGraph` constructs a complete graph with n vertices.
    A complete graph is a graph where every pair of distinct vertices is connected by an edge.

    ## Implementation notes
    * Edges are labelled as `Sym2` pairs with the `IsDiag` condition ensuring no self-loops
    * The `inc` function simply maps the edge to its label
-/
def CompleteGraph (n : ℕ) : Graph (Fin n) {e : Sym2 (Fin n) // ¬ e.IsDiag} where
  inc e := undir e

instance instCompleteGraphSimple (n : ℕ) : Simple (CompleteGraph n) where
  all_full _ := by simp only [isFull, edge.isFull, CompleteGraph]
  no_loops e := by simp only [isLoop, edge.isLoop, CompleteGraph, e.prop, not_false_eq_true]
  edge_symm _ := by simp only [isUndir, edge.isUndir, CompleteGraph]
  inc_inj e₁ e₂ h := by
    simp only [CompleteGraph, undir.injEq] at h
    exact Subtype.eq h

@[simp]
lemma CompleteGraph.adj {n : ℕ} {u v : Fin n} : (CompleteGraph n).adj u v ↔ u ≠ v := by
  constructor
  · rintro ⟨e, h⟩
    simp [CompleteGraph, canGo] at h
    have := h ▸ e.prop
    rwa [Sym2.mk_isDiag_iff] at this
  · intro h
    use ⟨s(u, v), by simp only [Sym2.isDiag_iff_proj_eq, h, not_false_eq_true]⟩
    simp only [canGo, CompleteGraph, undir_canGo]

/-- `PathGraph` constructs a path graph with n+1 vertices and n edges.
    A path graph is a graph where vertices are arranged in a line, with each vertex connected to its
    successor.

    ## Implementation notes
    * Vertices are labeled from 0 to n using `Fin (n+1)`
    * Edges are labeled from 0 to n-1 using `Fin n`, where edge i connects vertices i and i+1
    * The `inc` function maps each edge i to the undirected pair (i, i+1)
-/
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
    glue (EdgelessGraph_Emb (PathGraph n)
      ⟨(fun _ => Fin.last n : Fin 1 → Fin (n+1)), Function.injective_of_subsingleton _⟩)
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
      EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk, EdgelessGraph_Emb_fₑ, glue,
      Set.range_const, Set.mem_singleton_iff, Fin.ext_iff', Fin.val_zero, map_inc, add_inc,
      map_undir, Sym2.map_pair_eq, Fin.castLE_castSucc, Fin.castLE_succ, undir.injEq, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Fin.coe_castSucc, Fin.coe_castLE, and_self, Prod.swap_prod_mk,
      Fin.val_succ, self_eq_add_right, one_ne_zero, add_right_eq_self, or_false]
    | Sum.inr ⟨⟨e, he⟩, hemem⟩ => by
      cases e <;> simp [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.natAdd_mk,
        add_zero, Fin.castSucc_mk, Fin.succ_mk, EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk,
        EdgelessGraph_Emb_fₑ, glue, Set.range_const, Set.mem_singleton_iff, Fin.ext_iff',
        Fin.val_zero, map_inc, add_inc, Fin.zero_eta, zero_add, map_undir, Sym2.map_pair_eq,
        ↓reduceDIte, one_ne_zero, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Fin.coe_castLE, Fin.val_last, and_self, Prod.swap_prod_mk, self_eq_add_right,
        add_right_eq_self, or_false]
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
      simp only [Fin.natAdd_mk, Fin.castLE_mk, Fin.ext_iff', EdgelessGraph_Emb_fᵥ,
        Function.Embedding.coeFn_mk, Set.range_const, Set.mem_compl_iff, Set.mem_singleton_iff,
        Fin.val_zero] at h hwmem
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
    simp only [EdgelessGraph_Emb_fᵥ, Function.Embedding.coeFn_mk, Fin.ext_iff', Sum.exists,
      Fin.coe_castLE, Fin.coe_natAdd, Subtype.exists, Set.range_const, Set.mem_compl_iff,
      Set.mem_singleton_iff, Fin.val_zero, exists_prop]
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


/-- `CycleGraph n` is the graph with `n` vertices arranged in a cycle, where each vertex is
  connected to the next vertex (modulo n).

For example:
- `CycleGraph 3` is a triangle
- `CycleGraph 4` is a square
- `CycleGraph 5` is a pentagon

The vertices are labeled `0` through `n-1`, with edges between consecutive vertices and between
  `n-1` and `0`.
-/
def CycleGraph (n : ℕ) [NeZero n] : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)

instance instCycleGraphUndirected (n : ℕ) [NeZero n] : Undirected (CycleGraph n) where
  edge_symm _ := by simp [CycleGraph]
  all_full _ := by simp only [isFull, edge.isFull, CycleGraph]

@[simp]
lemma CycleGraph_get (n : ℕ) [NeZero n] (e : Fin n) : (CycleGraph n).get e = s(e, e+1) := by
  simp only [get, CycleGraph, undir.injEq, Classical.choose_eq']

lemma CycleGraph_isLoop_iff (n : ℕ) [NeZero n] : (CycleGraph n).isLoop 0 ↔ n = 1 := by
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

def CycleGraph.rotate (n : ℕ) [NeZero n] (k : Fin n) : CycleGraph n ≃ᴳ CycleGraph n where
  fᵥ v := v + k
  fₑ e := e + k
  inc e := by simp only [CycleGraph, map_undir, Sym2.map_pair_eq, add_right_comm]
  fᵥinj := add_left_injective k
  fₑinj := add_left_injective k
  fᵥsurj := add_right_surjective k
  fₑsurj := add_right_surjective k

@[simp]
lemma CycleGraph_rotate_fᵥ (n : ℕ) [NeZero n] (k : Fin n) : (CycleGraph.rotate n k).fᵥ = (· + k) := rfl

@[simp]
lemma CycleGraph_rotate_fₑ (n : ℕ) [NeZero n] (k : Fin n) : (CycleGraph.rotate n k).fₑ = (· + k) := rfl

@[simp]
lemma CycleGraph_rotate_symm_fᵥ (n : ℕ) [NeZero n] (k : Fin n) : (CycleGraph.rotate n k).symm.fᵥ = (· - k) := by
  ext1 v
  apply_fun (CycleGraph.rotate n k).fᵥ using (CycleGraph.rotate n k).fᵥinj
  simp only [Isom.fᵥ_symm_fᵥ, CycleGraph_rotate_fᵥ, sub_add_cancel]

@[simp]
lemma CycleGraph_rotate_symm_fₑ (n : ℕ) [NeZero n] (k : Fin n) : (CycleGraph.rotate n k).symm.fₑ = (· - k) := by
  ext1 e
  apply_fun (CycleGraph.rotate n k).fₑ using (CycleGraph.rotate n k).fₑinj
  simp only [Isom.fₑ_symm_fₑ, CycleGraph_rotate_fₑ, sub_add_cancel]

def CycleGraph.toPathGraph (n : ℕ) [NeZero n] :
    (CycleGraph n){{-1}ᶜ}ᴳ.valEs rfl ≃ᴳ PathGraph (n-1) where
  fᵥ v := ⟨v.val, by simp only [Fin.val_last', toSubgraph_val_Sᵥ, Nat.sub_one_add_one_eq_self,
    Fin.is_lt]⟩
  fₑ e := ⟨e.val, by
    have := e.prop
    simp only [Fin.neg_one_eq_last', toSubgraph_val_Sₑ, Fin.val_last', Set.mem_compl_iff,
      Set.mem_singleton_iff, Fin.ext_iff'] at this
    omega⟩
  inc e := by
    simp only [PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.castSucc_mk, Fin.succ_mk,
      Subgraph.valEs, Subgraph.toGraph, CycleGraph, Es_val_Sᵥ, Equiv.Set.univ_apply, Es_val_Sₑ,
      Equiv.refl_symm, Equiv.refl_apply, pmap_undir, Sym2.pmap_eq_pmap_of_imp, Sym2.pmap_pair,
      map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Fin.ext_iff',
      true_and, Prod.swap_prod_mk, add_right_eq_self, one_ne_zero, and_false, or_false]
    have := e.prop
    simp only [Fin.neg_one_eq_last', toSubgraph_val_Sₑ, -Fin.val_last', Set.mem_compl_iff,
      Set.mem_singleton_iff, -Fin.ext_iff'] at this
    rw [eq_comm, Fin.val_add_one']
    simp only [this, ↓reduceIte]
  fᵥinj v w h := by
    ext
    simpa only [Fin.val_last', toSubgraph_val_Sᵥ, Fin.ext_iff'] using h
  fₑinj e f h := by
    ext
    simpa only [Fin.val_last', toSubgraph_val_Sₑ, Fin.ext_iff'] using h
  fᵥsurj v := by
    simp only [Fin.val_last', toSubgraph_val_Sᵥ, Fin.ext_iff', Subtype.exists, Set.mem_univ,
      exists_const]
    use v
    rw [Fin.val_cast_of_lt]
    have := v.prop
    nth_rw 2 [Nat.sub_add_cancel NeZero.one_le] at this
    exact this
  fₑsurj e := by
    simp only [Fin.val_last', toSubgraph_val_Sₑ, Fin.ext_iff', Subtype.exists, Fin.neg_one_eq_last',
      Set.mem_compl_iff, Set.mem_singleton_iff, exists_prop]
    use e
    simp only [Fin.val_cast_of_lt (by omega : e < n), e.prop.ne, not_false_eq_true, and_self]

@[simp]
lemma CycleGraph_toPathGraph_fᵥ (n : ℕ) [NeZero n] : (CycleGraph.toPathGraph n).fᵥ =
    fun v ↦ ⟨v.val, by simp only [Fin.val_last', toSubgraph_val_Sᵥ, Nat.sub_one_add_one_eq_self,
    Fin.is_lt]⟩ := rfl

@[simp]
lemma CycleGraph_toPathGraph_fₑ (n : ℕ) [NeZero n] : (CycleGraph.toPathGraph n).fₑ =
    fun e ↦ ⟨e.val, by
    have := e.prop
    simp only [Fin.neg_one_eq_last', toSubgraph_val_Sₑ, Fin.val_last', Set.mem_compl_iff,
      Set.mem_singleton_iff, Fin.ext_iff'] at this
    omega⟩ := rfl

@[simp]
lemma CycleGraph_toPathGraph_symm_fᵥ (n : ℕ) [NeZero n] : (CycleGraph.toPathGraph n).symm.fᵥ =
    fun v ↦ ⟨v.val, by nth_rw 2 [← Nat.sub_one_add_one_eq_self n]; exact v.prop⟩ := by
  ext1 v
  apply_fun (CycleGraph.toPathGraph n).fᵥ using (CycleGraph.toPathGraph n).fᵥinj
  simp only [Isom.fᵥ_symm_fᵥ, CycleGraph_toPathGraph_fᵥ, Fin.ext_iff']

@[simp]
lemma CycleGraph_toPathGraph_symm_fₑ (n : ℕ) [NeZero n] : (CycleGraph.toPathGraph n).symm.fₑ =
    fun e ↦ ⟨e.val, by
    simp only [Fin.neg_one_eq_last', toSubgraph_val_Sₑ, Set.mem_compl_iff, Set.mem_singleton_iff,
      Fin.ext_iff', Fin.val_natCast, Fin.val_last']
    rw [Nat.mod_eq_of_lt (e.prop.trans (Nat.sub_lt NeZero.one_le Nat.one_pos))]
    exact e.prop.ne⟩ := by
  ext1 e
  apply_fun (CycleGraph.toPathGraph n).fₑ using (CycleGraph.toPathGraph n).fₑinj
  simp only [Isom.fₑ_symm_fₑ, CycleGraph_toPathGraph_fₑ, Fin.ext_iff']
  apply (Fin.val_cast_of_lt _).symm
  exact e.prop.trans (Nat.sub_lt NeZero.one_le Nat.one_pos)

def CycleGraph_Subgraph_singleton_comple_Isom_PathGraph (n : ℕ) [NeZero n] (i : Fin n) :
    (CycleGraph n){{i}ᶜ}ᴳ.valEs rfl ≃ᴳ PathGraph (n-1) := by
  let a := (CycleGraph n){{i}ᶜ}ᴳ
  let b := (CycleGraph n){{-1}ᶜ}ᴳ
  refine a.toGraph_Isom_toGraph.trans <|
    (a.Isom_of_equivOfIsom (CycleGraph.rotate n (-i - 1)) b ?_).trans
    (b.toGraph_Isom_toGraph.trans (CycleGraph.toPathGraph n))
  ext x <;> simp only [Fin.neg_one_eq_last', Es_val_Sᵥ, Set.mem_univ, Subgraph.mapByHom,
    CycleGraph_rotate_fᵥ, Set.image_add_right, neg_sub, sub_neg_eq_add, Set.preimage_univ,
    CycleGraph_rotate_fₑ, Es_val_Sₑ, Set.preimage_compl, Set.preimage_add_right_singleton,
    neg_add_rev, add_neg_cancel_left, b, a]

@[simp]
lemma CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_fᵥ (n : ℕ) [NeZero n] (i : Fin n) :
    (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fᵥ =
    fun v ↦ (v - i - 1).cast (Nat.sub_one_add_one_eq_self n).symm := by
  ext1 v
  simp only [Subgraph.valEs, CycleGraph_Subgraph_singleton_comple_Isom_PathGraph, Es_val_Sᵥ,
    Es_val_Sₑ, Subgraph.Isom_of_equivOfIsom, Subgraph.Emb_of_mapByHom, CycleGraph.rotate,
    Isom.trans_fᵥ, CycleGraph_toPathGraph_fᵥ, Subgraph.toGraph_Isom_toGraph_fᵥ, Equiv.refl_symm,
    Equiv.refl_trans, Subgraph.Hom_of_mapByHom_fᵥ, Equiv.trans_refl, Function.comp_apply,
    Equiv.Set.univ_symm_apply, Equiv.Set.univ_apply, Fin.ext_iff', Fin.coe_cast]
  ring_nf

@[simp]
lemma CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_fₑ (n : ℕ) [NeZero n] (i : Fin n) :
    (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fₑ =
    fun e ↦ (e.val - i - 1).castPred (by
    have := e.prop
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, -Fin.ext_iff'] at this
    contrapose! this
    simp only [Fin.ext_iff', Fin.val_natCast, Nat.sub_one_add_one_eq_self, Fin.val_last] at this
    rwa [← Fin.val_last', Nat.mod_eq_of_lt (by simp only [Fin.is_lt]), ← Fin.ext_iff,
      ← Fin.neg_one_eq_last', sub_toss_eq, neg_add_cancel, sub_toss_eq, zero_add] at this) := by
  ext1 v
  simp only [Subgraph.valEs, CycleGraph_Subgraph_singleton_comple_Isom_PathGraph, Es_val_Sᵥ,
    Es_val_Sₑ, Subgraph.Isom_of_equivOfIsom, Subgraph.Emb_of_mapByHom, CycleGraph.rotate,
    Isom.trans_fₑ, CycleGraph_toPathGraph_fₑ, Fin.val_last', toSubgraph_val_Sₑ,
    Subgraph.Hom_of_mapByHom_fₑ, Subgraph.toGraph_Isom_toGraph_fₑ, Equiv.refl_symm,
    Equiv.trans_refl, Equiv.coe_refl, Function.comp_apply, id_eq, Fin.ext_iff', Fin.coe_castPred,
    Fin.val_natCast, Nat.sub_one_add_one_eq_self]
  rw [Nat.mod_eq_of_lt (by simp only [Fin.is_lt]), ← Fin.ext_iff]
  ring

@[simp]
lemma CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_symm_fᵥ (n : ℕ) [NeZero n] (i : Fin n) :
    (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).symm.fᵥ =
    fun v ↦ (v.cast (Nat.sub_one_add_one_eq_self n) + 1 + i ) := by
  ext1 v
  apply_fun (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fᵥ
  simp only [Subgraph.valEs, Isom.fᵥ_symm_fᵥ,
    CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_fᵥ, add_sub_cancel_right, Fin.cast_trans,
    Fin.cast_eq_self]
  · exact (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fᵥinj

@[simp]
lemma CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_symm_fₑ (n : ℕ) [NeZero n] (i : Fin n) :
    (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).symm.fₑ =
    fun e ↦ ⟨(e.castSucc + 1 + i), by
    simp only [Fin.coe_castSucc, Set.mem_compl_iff, Set.mem_singleton_iff, add_left_eq_self,
      -Fin.ext_iff', Fin.val_zero]
    rw [Fin.add_one_eq_zero_iff]
    simp only [Fin.ext_iff', Fin.val_natCast, Fin.val_last']
    rw [Nat.mod_eq_of_lt (by omega)]
    exact e.prop.ne⟩ := by
  ext1 v
  apply_fun (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fₑ
  simp only [Subgraph.valEs, Isom.fₑ_symm_fₑ, Fin.coe_castSucc,
    CycleGraph_Subgraph_singleton_comple_Isom_PathGraph_fₑ, add_sub_cancel_right, Fin.val_natCast,
    Fin.ext_iff', Fin.coe_castPred, Nat.sub_one_add_one_eq_self, dvd_refl, Nat.mod_mod_of_dvd]
  rw [Nat.mod_eq_of_lt (by omega)]
  · exact (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph n i).fₑinj


-- def CycleGraph_Subgraph_singleton_comple_Isom_PathGraph (n : ℕ) [NeZero n] (i : Fin n) :
--     (CycleGraph n |>.toSubgraph Set.univ {i}ᶜ (by simp only [Set.mem_compl_iff,
--       Set.mem_singleton_iff, Fin.ext_iff', inc_eq_get, CycleGraph_get, mem_undir_iff, Sym2.mem_iff,
--       Set.mem_univ, implies_true])).val ≃ᴳ PathGraph (n-1) := by
--   let a := (CycleGraph n).toSubgraph Set.univ {i}ᶜ (by
--     simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff', inc_eq_get, CycleGraph_get,
--       mem_undir_iff, Sym2.mem_iff, Set.mem_univ, implies_true])
--   let b := (CycleGraph n).toSubgraph Set.univ {-1}ᶜ (by
--     simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff', inc_eq_get, CycleGraph_get,
--       mem_undir_iff, Sym2.mem_iff, Set.mem_univ, implies_true])
--   refine (a.Isom_of_equivOfIsom (CycleGraph.rotate n (-i - 1)) b ?_).trans
--     (CycleGraph.toPathGraph n)
--   ext x <;> simp only [Fin.neg_one_eq_last', toSubgraph_val_Sᵥ, Set.mem_univ, Subgraph.mapByHom,
--     CycleGraph_rotate_fᵥ, Set.image_add_right, neg_sub, sub_neg_eq_add, Set.preimage_univ,
--     CycleGraph_rotate_fₑ, toSubgraph_val_Sₑ, Set.preimage_compl, Set.preimage_add_right_singleton,
--     neg_add_rev, add_neg_cancel_left, b, a]

-- def CycleGraph_Isom_PathGraph_addUndirEdge (n : ℕ) {m : ℕ} [NeZero m] (hm : m = n + 1) :
--     (CycleGraph m).Isom (PathGraph n |>.addUndirEdge s(0, Fin.last _)) where
--   fᵥ := Fin.cast (by subst m; rfl)
--   fₑ e :=
--     if h : e = Fin.last n
--     then Sum.inr ()
--     else Sum.inl (e.castPred (by subst m; simp_all))
--   inc e := by
--     subst m
--     by_cases h : e = Fin.last n
--     · simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, h, Fin.val_last, Fin.natCast_eq_last,
--       ↓reduceDIte, addUndirEdge_inc_inr, CycleGraph, Fin.last_add_one, map_undir, Fin.cast_eq_self,
--       Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Fin.ext_iff',
--       Fin.val_zero, Prod.swap_prod_mk, or_true]
--     · simp only [addUndirEdge, PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ,
--       Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.val_last, Fin.natCast_eq_last, h, ↓reduceDIte,
--       Fin.cast_val_eq_self, Fin.castSucc_castPred, Fin.castPred_succ, Fin.cast_refl, CycleGraph,
--       map_undir, id_eq, Sym2.map_pair_eq]
--   fᵥinj _ _ a := by simpa using a
--   fₑinj e1 e2 h := by
--     subst m
--     by_cases he1 : e1 = Fin.last n <;> by_cases he2 : e2 = Fin.last n <;>
--     simp_all [Nat.succPNat_coe, Nat.succ_eq_add_one, dite_true, dite_false, Sum.inl_injective.eq_iff]
--   fᵥsurj _ := by subst m; simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, Fin.cast_eq_self,
--     Fin.ext_iff', exists_apply_eq_apply]
--   fₑsurj e := by
--     subst mn
--     simp
--     match e with
--     | Sum.inl e =>
--       use e
--       simp [e.prop.ne]
--     | Sum.inr () =>
--       use Fin.last _
--       simp


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
