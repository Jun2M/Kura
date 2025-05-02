import Kura.IncFun
import Mathlib.Combinatorics.SimpleGraph.Basic
import Kura.Dep.Sym2

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

section intro

-- This is mk'
-- def ofInc₂ (V : Set α) (isBtw : β → α → α → Prop) (hsymm : ∀ e x y, isBtw e x y → isBtw e y x)
--     (vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V)
--     (left_eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → x = u ∨ x = v) :
--     Graph α β where
--   V := V
--   E := {e | ∃ x y, isBtw e x y}
--   Inc₂ e x y := isBtw e x y
--   symm := hsymm
--   vx_mem_left := vx_mem_of_isBtw_left
--   edge_mem e x y hbtw := by use x, y
--   exists_vx_inc₂ e he := mem_setOf_eq.mp he
--   left_eq_of_inc₂ := left_eq_of_isBtw

-- variable {V : Set α} {isBtw : β → α → α → Prop} {h1 : ∀ e x y, isBtw e x y → isBtw e y x}
--     {h2 : ∀ e x y, isBtw e x y → x ∈ V}
--     {h3 : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → x = u ∨ x = v}

-- @[simp]
-- lemma ofInc₂_V : (ofInc₂ V isBtw h1 h2 h3).V = V := rfl

-- @[simp]
-- lemma ofInc₂_E : (ofInc₂ V isBtw h1 h2 h3).E = {e | ∃ x y, isBtw e x y} := rfl

-- @[simp]
-- lemma ofInc₂_inc₂ : (ofInc₂ V isBtw h1 h2 h3).Inc₂ = isBtw := rfl

-- @[simp]
-- lemma ofInc₂_inc : (ofInc₂ V isBtw h1 h2 h3).Inc = (∃ x, isBtw · · x) := rfl

-- protected def mk' (V : Set α) (Inc₂ : β → α → α → Prop)
--     (inc₂_symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x)
--     (eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w)
--     (vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V) : Graph α β where

def ofInc (V : Set α) (inc : β → α → Prop) (vx_mem : ∀ e v, inc e v → v ∈ V)
    (not_hypergraph : ∀ ⦃x y z e⦄, inc e x → inc e y → inc e z → x = y ∨ x = z ∨ y = z) :
    Graph α β := Graph.mk'
  (V := V)
  (Inc₂ := fun e x y ↦ inc e x ∧ inc e y ∧ ∀ z, inc e z → z = x ∨ z = y)
  (inc₂_symm := fun e x y h ↦ by
    obtain ⟨hx, hy, h_unique⟩ := h
    exact ⟨hy, hx, fun z hz ↦ (h_unique z hz).symm⟩)
  (eq_or_eq_of_inc₂_of_inc₂ := fun e a b c d  h1 h2 ↦ by
    obtain ⟨hinca, hincb, hinc_unique⟩ := h1
    obtain ⟨hincc, hincd, hinc_unique'⟩ := h2
    have := hinc_unique' a hinca
    have := hinc_unique' b hincb
    obtain rfl | rfl := hinc_unique c hincc <;> obtain rfl | rfl := hinc_unique d hincd <;> tauto)
  (vx_mem_left_of_inc₂ := fun e x y h ↦ by
    obtain ⟨hx, hy, h_unique⟩ := h
    exact vx_mem e x hx)

variable {V : Set α} {inc : β → α → Prop} {vx_mem : ∀ e v, inc e v → v ∈ V}
    {not_hypergraph : ∀ ⦃x y z e⦄, inc e x → inc e y → inc e z → x = y ∨ x = z ∨ y = z}

@[simp] lemma ofInc_V : (ofInc V inc vx_mem not_hypergraph).V = V := rfl

@[simp] lemma ofInc_E : (ofInc V inc vx_mem not_hypergraph).E = {e | ∃ x, inc e x} := by
  ext e
  simp only [ofInc, mk'_edgeSet, exists_and_left, mem_setOf_eq]
  refine ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  by_cases hy : ∃ y, x ≠ y ∧ inc e y
  · obtain ⟨y, hxy, hy⟩ := hy
    use x, hx, y, hy, fun z hz ↦ ?_
    specialize not_hypergraph hx hy hz
    tauto
  · simp only [ne_eq, not_exists, not_and] at hy
    use x, hx, x, hx, fun z hz ↦ ?_
    specialize hy z
    tauto

@[simp] lemma ofInc_inc : (ofInc V inc vx_mem not_hypergraph).Inc = inc := by
  unfold ofInc
  ext e v
  simp only [Inc, mk'_inc₂, exists_and_left, and_iff_left_iff_imp]
  rintro hincv
  by_cases h : ∃ x, x ≠ v ∧ inc e x
  · obtain ⟨x, hx, hincx⟩ := h
    use x, hincx
    rintro z hz
    specialize not_hypergraph hincv hincx hz
    tauto
  · simp only [ne_eq, not_exists, not_and] at h
    use v, hincv
    rintro z hz
    specialize h z
    tauto

@[simps]
def oftoMultiset (V : Set α) (toMultiset : β → Multiset α) (vx_mem : ∀ e v, v ∈ toMultiset e → v ∈ V) :
    Graph α β where
  V := V
  E := {e | (toMultiset e).card = 2}
  Inc₂ e x y := toMultiset e = {x, y}
  inc₂_symm e x y h := by rwa [Multiset.pair_comm]
  vx_mem_left_of_inc₂ e x y h := by
    refine vx_mem e x ?_
    rw [h]
    simp
  edge_mem_iff_exists_inc₂ e := by
    constructor
    · simp [mem_setOf_eq, Multiset.card_eq_two]
    · rintro ⟨x, y, hbtw⟩
      rw [mem_setOf_eq, hbtw]
      rfl
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    rw [h1, Multiset.pair_eq_pair_iff] at h2
    tauto

variable {toMultiset : β → Multiset α} {vx_mem : ∀ e v, v ∈ toMultiset e → v ∈ V}

@[simp]
lemma oftoMultiset_toMultiset (card_eq : ∀ e, (toMultiset e).card = 2 ∨ (toMultiset e).card = 0) :
    (oftoMultiset V toMultiset vx_mem).toMultiset = toMultiset := by
  ext e
  obtain h | h := card_eq e
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp h
    rwa [hxy, toMultiset_eq_pair_iff]
  · simp [Multiset.card_eq_zero.mp h]

@[simps]
def ofIncFun (V : Set α) (incFun : β → α →₀ ℕ) (vx_mem : ∀ e v, incFun e v ≠ 0 → v ∈ V) :
    Graph α β where
  V := V
  E := {e | (incFun e).sum (fun _ ↦ id) = 2}
  Inc₂ e x y := by
    classical
    exact ({x, y} : Multiset α).toFinsupp = incFun e
  inc₂_symm e x y h := by rwa [Multiset.pair_comm]
  vx_mem_left_of_inc₂ e x y h := vx_mem e x (by simp [← h])
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, hxy⟩ ↦ by simp [← hxy]⟩
    have : (incFun e).toMultiset.card = 2 := by simpa
    rw [Multiset.card_eq_two] at this
    obtain ⟨x, y, hxy⟩ := this
    use x, y
    simp only [← hxy, Finsupp.toMultiset_toFinsupp]
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    rw [← h2, EmbeddingLike.apply_eq_iff_eq, Multiset.pair_eq_pair_iff] at h1
    tauto

variable {incFun : β → α →₀ ℕ} {vx_mem : ∀ e v, incFun e v ≠ 0 → v ∈ V}

@[simp]
lemma ofIncFun_V : (ofIncFun V incFun vx_mem).V = V := rfl

@[simp]
lemma ofIncFun_E : (ofIncFun V incFun vx_mem).E = {e | (incFun e).sum (fun _ ↦ id) = 2} := rfl

@[simp]
lemma ofIncFun_incFun : (ofIncFun V incFun vx_mem).incFun = incFun := by
  -- classical
  -- ext e v
  -- rw [← toMultiset_count, ← inc₂_iff_toMultiset]
  sorry

@[simps]
def oftoSym2 (V : Set α) (E : Set β) (tosym2 : ∀ (e) (_he : e ∈ E), Sym2 α)
    (vx_mem : ∀ e v he, v ∈ tosym2 e he → v ∈ V) : Graph α β where
  V := V
  E := E
  Inc₂ e x y := ∃ (he : e ∈ E), tosym2 e he = s(x, y)
  inc₂_symm e x y h := by
    obtain ⟨he, hxy⟩ := h
    use he, Sym2.eq_swap ▸ hxy
  vx_mem_left_of_inc₂ e x y h := by
    obtain ⟨he, hxy⟩ := h
    exact vx_mem e x he (by simp [hxy])
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, he, hxy⟩ ↦ he⟩
    simp only [he, exists_true_left]
    induction' tosym2 e he with x y
    use x, y
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨he, h1⟩ := h1
    obtain ⟨he', h2⟩ := h2
    simp [h1] at h2
    tauto

variable {E : Set β} {tosym2 : ∀ (e) (_he : e ∈ E), Sym2 α}
  {vx_mem : ∀ e v he, v ∈ tosym2 e he → v ∈ V}

@[simp]
lemma oftoSym2_tosym2 : (oftoSym2 V E tosym2 vx_mem).toSym2 = tosym2 := by
  ext1 e; ext1 he
  rw [(tosym2 e he).eq_mk_out]
  rw [oftoSym2_edgeSet] at he
  simp only [oftoSym2, toSym2_eq_pair_iff]
  use he
  simp only [Prod.mk.eta, Quot.out_eq]

end intro


/-- The graph with vertex set `V` and no edges -/
@[simps] protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  V := V
  E := ∅
  Inc₂ _ _ _ := False
  inc₂_symm := by simp
  eq_or_eq_of_inc₂_of_inc₂ := by simp
  edge_mem_iff_exists_inc₂ := by simp
  vx_mem_left_of_inc₂ := by simp

@[simp]
lemma edge_empty_iff_eq_noEdge (G : Graph α β) : G.E = ∅ ↔ G = Graph.noEdge G.V β := by
  constructor <;> rintro h
  · refine Graph.ext rfl fun e x y ↦ ?_
    simp only [noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
    not_inc₂_of_not_mem_edgeSet, iff_false]
    rintro hinc
    have := h ▸ hinc.edge_mem
    simp at this
  · rw [h, noEdge_edgeSet]

@[simp]
lemma not_adj_noEdge : ¬ (Graph.noEdge S β).Adj x y := by
  rintro ⟨e, hbtw⟩
  revert hbtw
  simp

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  V := {u,v}
  E := {e}
  Inc₂ e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  inc₂_symm := by tauto
  eq_or_eq_of_inc₂_of_inc₂ := by aesop
  edge_mem_iff_exists_inc₂ := by tauto
  vx_mem_left_of_inc₂ := by tauto

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma singleEdge_inc₂_iff : (Graph.singleEdge u v e).Inc₂ f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]


/-- The graph induced by a simple graph -/
def ofSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  V := univ
  E := G.edgeSet
  Inc₂ e x y := s(x,y) = e ∧ G.Adj x y
  inc₂_symm e x y := by simp [Sym2.eq_swap, SimpleGraph.adj_comm]
  vx_mem_left_of_inc₂ e x y := by simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, hx, he⟩ ↦ by simp [he, ← hx]⟩
    induction' e with x y
    use x, y
    simpa using he
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨rfl, he⟩ := h1
    obtain ⟨heq, he'⟩ := h2
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto
