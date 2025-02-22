import Kura.Graph.FullGraph


namespace Graph
open edge
variable {V W E F : Type*} {G : Graph V E} [Undirected G] {H : Graph W F} [Undirected H] (e : E) (u v w : V)


-- def get : Sym2 V := match h : G.inc e with
--   | dir (a, b) => (not_isUndir_of_dir (a, b) (h ▸ G.edge_symm e)).elim
--   | undir s => s

-- @[simp]
-- lemma mem_get_iff_mem_inc : v ∈ G.inc e ↔ v ∈ G.get e := by
--   match h : G.inc e with
--   | dir (a, b) =>
--     have := Undirected.edge_symm (G := G) e
--     cases a <;> cases b <;> simp_all only [isUndir, not_isUndir_of_dir, Bool.false_eq_true]
--   | undir s =>
--     simp [get, h]
--     split <;> simp_all

-- @[simp low]
-- lemma inc_eq_undir_get : G.inc e = undir (G.get e) := by
--   match h : G.inc e with
--   | dir (a, b) =>
--     have := Undirected.edge_symm (G := G) e
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

def ofIsLoop {e : E} (he : G.isLoop e) : V := (G.inc e).ofIsLoop he

omit [Undirected G] in
lemma ofIsLoop_mem (he : G.isLoop e) : G.ofIsLoop he ∈ G.inc e := (G.inc e).ofIsLoop_mem he

lemma inc_eq_ofIsLoop (he : G.isLoop e) : G.inc e = undir s(G.ofIsLoop he, G.ofIsLoop he) :=
  edge.eq_ofIsLoop_of_undir he (G.edge_symm e)

@[simp]
lemma v1_eq_ofIsLoop (he : G.isLoop e) : G.v1 e = G.ofIsLoop he := edge.v1_eq_ofIsLoop he

@[simp]
lemma v2_eq_ofIsLoop (he : G.isLoop e) : G.v2 e = G.ofIsLoop he := edge.v2_eq_ofIsLoop he

noncomputable def get' : Sym2 V := (exist_of_isUndir (G.edge_symm e)).choose

def get : Sym2 V := match h : G.inc e with
  | dir (a, b) => (not_isUndir_of_dir (a, b) (h ▸ G.edge_symm e)).elim
  | undir s => s

lemma inc_eq_undir_v12 : G.inc e = undir s(G.v1 e, G.v2 e) := by
  match h : G.inc e with
  | dir (a, b) =>
    have := Undirected.edge_symm (G := G) e
    rw [isUndir, h] at this
    exact (not_isUndir_of_dir _ this).elim
  | undir s =>
    simp only [v1, h, undir_v1, v2, undir_v2, Prod.mk.eta, Quot.out_eq]

lemma get_eq_v12 : G.get e = s(G.v1 e, G.v2 e) := by
  -- simp only [get, inc_eq_undir_v12, undir.injEq, Classical.choose_eq']
  unfold get
  split
  · rename_i a b h
    rw [inc_eq_undir_v12] at h
    simp only [reduceCtorEq] at h
  · rename_i s h
    rw [inc_eq_undir_v12, eq_comm] at h
    simpa only [undir.injEq] using h

@[simp]
lemma inc_eq_get (e : E) : G.inc e = undir (G.get e) := by
  -- simp only [inc_eq_undir_v12, get, undir.injEq, Classical.choose_eq']
  unfold get
  split
  · rename_i a b h
    rw [inc_eq_undir_v12] at h
    simp only [reduceCtorEq] at h
  · assumption

lemma get_eq_iff_canGo [DecidableEq V] {v w : V} {e : E} : G.get e = s(v, w) ↔ G.canGo v e w := by
  simp only [get, canGo, inc_eq_get, canGo_iff_eq_of_undir]

lemma lift_v12 {α : Type*} {f : V → V → α} (hf : ∀ (a₁ a₂ : V), f a₁ a₂ = f a₂ a₁) (e : E) :
    f (G.v1 e) (G.v2 e) = Sym2.lift ⟨f, hf⟩ (G.get e) := by
  simp only [get_eq_v12, Sym2.lift_mk]

lemma Hom.get (A : G ⊆ᴳ H) (e : E) : H.get (A.fₑ e) = (G.get e).map A.fᵥ := by
  have := A.inc e
  rwa [inc_eq_get, inc_eq_get, edge.map_undir, undir.injEq] at this

lemma canGo_symm [DecidableEq V] : G.canGo u e v = G.canGo v e u := by
  simp only [canGo, inc_eq_undir_v12]
  rw [← canGo_flip, flip_self]

-- lemma canGo_iff_eq_v12 [DecidableEq V] : G.canGo u e v ↔ G.v1 e = u ∧ G.v2 e = v ∨
--     G.v1 e = v ∧ G.v2 e = u := by
--   simp only [canGo, inc_eq_undir_v12, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
--     Prod.swap_prod_mk]

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

omit [Undirected H] in
lemma Emb.Undirected' (hGH : H ⊆ᴳ G) : Undirected H where
  all_full e := by
    unfold isFull
    rw [← map_isFull_iff, ← hGH.inc e]
    exact all_full G (hGH.fₑ e)
  edge_symm e := by
    unfold isUndir
    rw [← map_isUndir_iff, ← hGH.inc e]
    exact edge_symm G _

lemma Emb_v12 (A : G ⊆ᴳ H) (e : E) : H.v1 (A.fₑ e) = A.fᵥ (G.v1 e) ∧ H.v2 (A.fₑ e) =
    A.fᵥ (G.v2 e) ∨ H.v1 (A.fₑ e) = A.fᵥ (G.v2 e) ∧ H.v2 (A.fₑ e) = A.fᵥ (G.v1 e) := by
  have := A.inc e
  simp only [inc_eq_undir_v12, map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff',
    Prod.mk.injEq, Prod.swap_prod_mk] at this
  exact this

-- lemma Emb_v12' (A : G ⊆ᴳ H) (e : E) : H.v1 (A.fₑ e) = A.fᵥ (G.v1 e) ∧ H.v2 (A.fₑ e) =
--     A.fᵥ (G.v2 e) ∨ H.v1 (A.fₑ e) = A.fᵥ (G.v2 e) ∧ H.v2 (A.fₑ e) = A.fᵥ (G.v1 e) := by
--   have := A.inc e
--   simp [-inc_eq_undir_v12, map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.eq, Sym2.rel_iff',
--     Prod.mk.injEq, Prod.swap_prod_mk] at this
--   exact this
end Graph

namespace Graph
variable {G : Graph V E} [Simple G]

@[simp]
lemma inc_inj_iff {e e' : E} : G.inc e = G.inc e' ↔ e = e' := by
  constructor
  · apply G.inc_inj
  · rintro rfl
    rfl

lemma get_injective : Function.Injective G.get := by
  rintro e f h
  apply G.inc_inj
  rw [inc_eq_get, inc_eq_get, h]

@[simp]
lemma get_inj_iff {e e' : E} : G.get e = G.get e' ↔ e = e' := by
  constructor
  · apply get_injective
  · rintro rfl
    rfl



end Graph
