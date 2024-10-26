import Kura.Graph.FullGraph


namespace Graph
open edge
variable {V W E F : Type*} {G : Graph V E} [Undirected G] (e : E) (u v w : V)


-- def get : Sym2 V :=
--   match h : G.inc e with
--   | dir (a, b) => by
--     have := Undirected.edge_symm (G := G) e
--     rw [isUndir, h] at this
--     exact (not_isUndir_of_dir _ this).elim
--   | undir s => s

-- @[simp]
-- lemma mem_get_iff_mem_inc : v ∈ G.inc e ↔ v ∈ G.get e := by
--   match h : G.inc e with
--   | dir (a, b) =>
--     have := @Undirected.edge_symm _ _ _ G _ e
--     cases a <;> cases b <;> simp_all only [isUndir, not_isUndir_of_dir, Bool.false_eq_true]
--   | undir s =>
--     simp [get, h]
--     split <;> simp_all

-- @[simp low]
-- lemma inc_eq_undir_get : G.inc e = undir (G.get e) := by
--   match h : G.inc e with
--   | dir (a, b) =>
--     have := @Undirected.edge_symm _ _ _ G _ e
--     cases a <;> cases b <;> simp_all
--   | undir s =>
--     simp only [get, h]
--     split <;> simp_all

-- @[simp]
-- lemma get_inf_mem_inc : (G.get e).inf ∈ G.inc e := by
--   simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
--     List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
--     Sym2.inf_mem]

-- @[simp]
-- lemma get_sup_mem_inc : (G.get e).sup ∈ G.inc e := by
--   simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
--     List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
--     Sym2.sup_mem]

-- @[simp]
-- lemma mem_startAt_iff_mem_get : v ∈ G.startAt e ↔ v ∈ G.get e := by
--   simp only [startAt, inc_eq_undir_get, mem_startAt_undir]

-- @[simp]
-- lemma mem_finishAt_iff_mem_get : v ∈ G.finishAt e ↔ v ∈ G.get e := by
--   simp only [finishAt, inc_eq_undir_get, mem_finishAt_undir]

@[simp high]
lemma inc_eq_undir_v12 : G.inc e = undir s(G.v1 e, G.v2 e) := by
  match h : G.inc e with
  | dir (a, b) =>
    have := Undirected.edge_symm (G := G) e
    rw [isUndir, h] at this
    exact (not_isUndir_of_dir _ this).elim
  | undir s =>
    simp only [v1, h, undir_v1, v2, undir_v2, Prod.mk.eta, Quot.out_eq]

lemma canGo_symm [DecidableEq V] : G.canGo u e v = G.canGo v e u := by
  simp only [canGo, inc_eq_undir_v12]
  rw [← canGo_flip, flip_self]

lemma canGo_iff_eq_v12 [DecidableEq V] : G.canGo u e v ↔ (u = G.v1 e ∧ v = G.v2 e) ∨ (u = G.v2 e ∧ v = G.v1 e) := by
  simp only [canGo, inc_eq_undir_v12]
  constructor
  · rintro h

    sorry
  ·
    sorry

lemma startAt_eq_endAt : G.startAt e = G.endAt e := by
  simp only [startAt, inc_eq_undir_v12, undir_startAt, endAt, undir_endAt]

lemma finishAt_eq_endAt : G.finishAt e = G.endAt e := by
  simp only [finishAt, inc_eq_undir_v12, undir_finishAt, endAt, undir_endAt]

noncomputable def goFrom [DecidableEq V] {v : V} {e : E} (h : v ∈ s(G.v1 e, G.v2 e)) : V :=
  Sym2.Mem.other' h


lemma mem_incEE_symm [DecidableEq V] (h : e' ∈ G.incEE e) : e ∈ G.incEE e' := by
  rw [incEE, Set.mem_setOf_eq] at h ⊢
  obtain ⟨ rfl, h ⟩ | ⟨ h1, h2 ⟩ := h
  · simp only [isLoop, inc_eq_undir_v12, undir_isLoop_iff] at h
    left
    simp only [isLoop, inc_eq_undir_v12, undir_isLoop_iff, h, and_self]
  · right
    rw [Multiset.inter_comm, startAt_eq_endAt, finishAt_eq_endAt] at h2
    rw [startAt_eq_endAt, finishAt_eq_endAt]
    refine ⟨ h1.symm, h2 ⟩

lemma mem_incEE_of_both_mem_incVE [DecidableEq V] (hne : e ≠ e') (h : e ∈ G.incVE v)
  (h' : e' ∈ G.incVE v) : e' ∈ G.incEE e := by
  simp only [incVE, startAt, inc_eq_undir_v12, undir_startAt, Multiset.empty_eq_zero,
    Set.mem_setOf_eq, incEE, isLoop, undir_isLoop_iff, finishAt, undir_finishAt] at h h' ⊢
  right
  refine ⟨ hne, ?_ ⟩
  exact Multiset.ne_zero_of_mem <| Multiset.mem_inter.mpr ⟨ h, h' ⟩

lemma adj_comm [DecidableEq V] : G.adj u v ↔ G.adj v u := by
  simp only [adj, canGo_symm]
