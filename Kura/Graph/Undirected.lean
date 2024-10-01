import Kura.Graph.Defs


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] {G : Graph V E} [Undirected G] (e : E) (u v w : V)


def get : Sym2 V :=
  match h : G.inc e with
  | dir (a, b) => by
    have := Undirected.edge_symm (G := G) e
    rw [isUndir, h] at this
    exact (not_isUndir_of_dir _ _ this).elim
  | undir s => s

@[simp]
lemma mem_get_iff_mem_inc : v ∈ G.inc e ↔ v ∈ G.get e := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all only [isUndir, not_isUndir_of_dir, Bool.false_eq_true]
  | undir s =>
    simp [get, h]
    split <;> simp_all

@[simp low]
lemma inc_eq_undir_get : G.inc e = undir (G.get e) := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all
  | undir s =>
    simp only [get, h]
    split <;> simp_all

lemma canGo_symm : G.canGo u e v = G.canGo v e u := by
  simp only [canGo, inc_eq_undir_get]
  rw [← canGo_flip, flip_self]

@[simp]
lemma get_inf_mem_inc : (G.get e).inf ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.inf_mem]

@[simp]
lemma get_sup_mem_inc : (G.get e).sup ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.sup_mem]

@[simp]
lemma mem_startAt_iff_mem_get : v ∈ G.startAt e ↔ v ∈ G.get e := by
  simp only [startAt, inc_eq_undir_get, mem_startAt_undir]

@[simp]
lemma mem_finishAt_iff_mem_get : v ∈ G.finishAt e ↔ v ∈ G.get e := by
  simp only [finishAt, inc_eq_undir_get, mem_finishAt_undir]


def goFrom {v : V} {e : E} (h : v ∈ G.get e) : V := Sym2.Mem.other' h
