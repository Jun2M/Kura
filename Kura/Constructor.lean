import Kura.Graph

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

section intro

def ofInc₂ (V : Set α) (isBtw : β → α → α → Prop) (hsymm : ∀ e x y, isBtw e x y → isBtw e y x)
    (vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V)
    (left_eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → x = u ∨ x = v) :
    Graph α β where
  V := V
  E := {e | ∃ x y, isBtw e x y}
  Inc₂ e x y := isBtw e x y
  symm := hsymm
  vx_mem_left := vx_mem_of_isBtw_left
  edge_mem e x y hbtw := by use x, y
  exists_vx_inc₂ e he := mem_setOf_eq.mp he
  left_eq_of_inc₂ := left_eq_of_isBtw

variable {V : Set α} {isBtw : β → α → α → Prop} {h1 : ∀ e x y, isBtw e x y → isBtw e y x}
    {h2 : ∀ e x y, isBtw e x y → x ∈ V}
    {h3 : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → x = u ∨ x = v}

@[simp]
lemma ofInc₂_V : (ofInc₂ V isBtw h1 h2 h3).V = V := rfl

@[simp]
lemma ofInc₂_E : (ofInc₂ V isBtw h1 h2 h3).E = {e | ∃ x y, isBtw e x y} := rfl

@[simp]
lemma ofInc₂_inc₂ : (ofInc₂ V isBtw h1 h2 h3).Inc₂ = isBtw := rfl

@[simp]
lemma ofInc₂_inc : (ofInc₂ V isBtw h1 h2 h3).Inc = (∃ x, isBtw · · x) := rfl


def ofInc (V : Set α) (inc : β → α → Prop) (vx_mem : ∀ e v, inc e v → v ∈ V)
    (not_hypergraph : ∀ ⦃x y z e⦄, inc e x → inc e y → inc e z → x = y ∨ y = z ∨ x = z) :
    Graph α β where
  V := V
  E := {e | ∃ x, inc e x}
  Inc₂ e x y := inc e x ∧ inc e y ∧ ∀ z, inc e z → z = x ∨ z = y
  symm e x y h := by
    obtain ⟨hx, hy, h_unique⟩ := h
    exact ⟨hy, hx, fun z hz ↦ (h_unique z hz).symm⟩
  vx_mem_left e x y h := by
    obtain ⟨hx, hy, h_unique⟩ := h
    exact vx_mem e x hx
  edge_mem e x y hbtw := by
    obtain ⟨hx, hy, h_unique⟩ := hbtw
    use x
  exists_vx_inc₂ e he := by
    obtain ⟨x, hx⟩ := he
    by_cases hy : ∃ y, x ≠ y ∧ inc e y
    · obtain ⟨y, hxy, hy⟩ := hy
      use x, y, hx, hy
      rintro z hz
      specialize not_hypergraph hx hy hz
      tauto
    · simp only [ne_eq, not_exists, not_and] at hy
      use x, x, hx, hx
      rintro z hz
      specialize hy z
      tauto
  left_eq_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨hinca, hincb, hinc_unique⟩ := h1
    obtain ⟨hincc, hincd, hinc_unique'⟩ := h2
    obtain rfl | rfl := hinc_unique c hincc <;>
    obtain rfl | rfl := hinc_unique d hincd
    · specialize hinc_unique' b hincb
      tauto
    · tauto
    · tauto
    · specialize hinc_unique' a hinca
      tauto

variable {inc : β → α → Prop} {vx_mem : ∀ e v, inc e v → v ∈ V}
    {not_hypergraph : ∀ ⦃x y z e⦄, inc e x → inc e y → inc e z → x = y ∨ y = z ∨ x = z}

@[simp] lemma ofInc_V : (ofInc V inc vx_mem not_hypergraph).V = V := rfl

@[simp] lemma ofInc_E : (ofInc V inc vx_mem not_hypergraph).E = {e | ∃ x, inc e x} := rfl

@[simp] lemma ofInc_inc : (ofInc V inc vx_mem not_hypergraph).Inc = inc := by
  unfold ofInc
  ext e v
  simp only [Inc, exists_and_left, and_iff_left_iff_imp]
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


def oftoMultiset (V : Set α) (toMultiset : β → Multiset α) (vx_mem : ∀ e v, v ∈ toMultiset e → v ∈ V) :
    Graph α β where
  V := V
  E := {e | (toMultiset e).card = 2}
  Inc₂ e x y := toMultiset e = {x, y}
  symm e x y h := by
    simp only at h ⊢
    rwa [Multiset.pair_comm]
  vx_mem_left e x y h := by
    refine vx_mem e x ?_
    rw [h]
    simp
  edge_mem e x y hbtw := by
    rw [mem_setOf_eq, hbtw]
    rfl
  exists_vx_inc₂ e he := by
    rw [mem_setOf_eq, Multiset.card_eq_two] at he
    obtain ⟨x, y, hxy⟩ := he
    use x, y
  left_eq_of_inc₂ a b c d e h1 h2 := by
    simp only at h1 h2
    rw [h1, Multiset.pair_eq_pair_iff] at h2
    tauto

variable {toMultiset : β → Multiset α} {vx_mem : ∀ e v, v ∈ toMultiset e → v ∈ V}

@[simp] lemma oftoMultiset_V : (oftoMultiset V toMultiset vx_mem).V = V := rfl

@[simp]
lemma oftoMultiset_E : (oftoMultiset V toMultiset vx_mem).E = {e | (toMultiset e).card = 2} := rfl

@[simp]
lemma oftoMultiset_toMultiset (card_eq : ∀ e, (toMultiset e).card = 2 ∨ (toMultiset e).card = 0) :
    (oftoMultiset V toMultiset vx_mem).toMultiset = toMultiset := by
  ext e
  unfold oftoMultiset
  obtain h | h := card_eq e
  · rw [Multiset.card_eq_two] at h
    obtain ⟨x, y, hxy⟩ := h
    rwa [hxy, ← inc₂_iff_toMultiset]
  · rw [Multiset.card_eq_zero] at h
    simp [h]


def ofIncFun (V : Set α) (incFun : β → α →₀ ℕ) (vx_mem : ∀ e v, incFun e v ≠ 0 → v ∈ V) :
    Graph α β where
  V := V
  E := {e | (incFun e).sum (fun _ ↦ id) = 2}
  Inc₂ e x y := by
    classical
    exact ({x, y} : Multiset α).toFinsupp = incFun e
  symm e x y h := by
    simp only at h ⊢
    rwa [Multiset.pair_comm]
  vx_mem_left e x y h := by
    refine vx_mem e x ?_
    rw [← h]
    simp
  edge_mem e x y hbtw := by simp [← hbtw]
  exists_vx_inc₂ e he := by
    classical
    simp only
    have : (incFun e).toMultiset.card = 2 := by simpa
    rw [Multiset.card_eq_two] at this
    obtain ⟨x, y, hxy⟩ := this
    use x, y
    rw [← hxy, Finsupp.toMultiset_toFinsupp]
  left_eq_of_inc₂ a b c d e h1 h2 := by
    simp only at h1 h2
    rw [← h2, EmbeddingLike.apply_eq_iff_eq, Multiset.pair_eq_pair_iff] at h1
    tauto

variable {incFun : β → α →₀ ℕ} {vx_mem : ∀ e v, incFun e v ≠ 0 → v ∈ V}

@[simp]
lemma ofIncFun_V : (ofIncFun V incFun vx_mem).V = V := rfl

@[simp]
lemma ofIncFun_E : (ofIncFun V incFun vx_mem).E = {e | (incFun e).sum (fun _ ↦ id) = 2} := rfl

@[simp]
lemma ofIncFun_incFun : (ofIncFun V incFun vx_mem).IncFun = incFun := by
  -- classical
  -- ext e v
  -- rw [← toMultiset_count, ← inc₂_iff_toMultiset]
  sorry

def oftoSym2 (V : Set α) (E : Set β) (tosym2 : ∀ (e) (_he : e ∈ E), Sym2 α)
    (vx_mem : ∀ e v he, v ∈ tosym2 e he → v ∈ V) : Graph α β where
  V := V
  E := E
  Inc₂ e x y := ∃ (he : e ∈ E), tosym2 e he = s(x, y)
  symm e x y h := by
    obtain ⟨he, hxy⟩ := h
    use he, Sym2.eq_swap ▸ hxy
  vx_mem_left e x y h := by
    obtain ⟨he, hxy⟩ := h
    exact vx_mem e x he (by simp [hxy])
  edge_mem e x y hbtw := by
    obtain ⟨he, hxy⟩ := hbtw
    use he
  exists_vx_inc₂ e he := by
    simp only [he, exists_true_left]
    induction' tosym2 e he with x y
    use x, y
  left_eq_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨he, h1⟩ := h1
    obtain ⟨he', h2⟩ := h2
    simp [h1] at h2
    tauto

variable {E : Set β} {tosym2 : ∀ (e) (_he : e ∈ E), Sym2 α}
  {vx_mem : ∀ e v he, v ∈ tosym2 e he → v ∈ V}

@[simp]
lemma oftoSym2_V : (oftoSym2 V E tosym2 vx_mem).V = V := rfl

@[simp]
lemma oftoSym2_E : (oftoSym2 V E tosym2 vx_mem).E = E := rfl

@[simp]
lemma oftoSym2_tosym2 : (oftoSym2 V E tosym2 vx_mem).toSym2 = tosym2 := by
  ext1 e; ext1 he
  rw [(tosym2 e he).eq_mk_out]
  rw [oftoSym2_E] at he
  simp only [oftoSym2, toSym2.eq_iff_inc₂]
  use he
  simp only [Prod.mk.eta, Quot.out_eq]

end intro


def Edgeless (V : Set α) (β : Type*) : Graph α β := ofInc V (fun _ _ ↦ False) (by tauto) (by tauto)

namespace Edgeless

@[simp] lemma V : (Edgeless U β).V = U := rfl

@[simp] lemma E : (Edgeless U β).E = ∅ := by simp [Edgeless]

@[simp] lemma incFun : (Edgeless U β).IncFun = 0 := by simp

@[simp] lemma Inc  : ¬ (Edgeless U β).Inc e v  := by simp

@[simp] lemma Inc₂ : ¬ (Edgeless U β).Inc₂ e u v := by simp

@[simp] lemma Adj : ¬ (Edgeless U β).Adj x y := by simp

end Edgeless

@[simp]
lemma edge_empty_iff_eq_Edgeless (G : Graph α β) : G.E = ∅ ↔ G = Edgeless G.V β := by
  constructor
  · rintro h
    ext1
    · rfl
    · simpa
    · ext e v
      simp only [Edgeless.E, mem_empty_iff_false, not_false_eq_true, not_inc₂_of_not_edge_mem,
        iff_false]
      rintro hinc
      have := h ▸ hinc.edge_mem
      simp at this
  · rintro heq
    rw [heq, Edgeless.E]

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps] protected def singleEdge (u v : α) (e : β) : Graph α β where
  V := {u,v}
  E := {e}
  Inc₂ e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  symm := by tauto
  vx_mem_left := by tauto
  edge_mem := by tauto
  exists_vx_inc₂ := by tauto
  left_eq_of_inc₂ := by aesop

lemma singleEdge_inc₂_iff : (Graph.singleEdge u v e).Inc₂ f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]
