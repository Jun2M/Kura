import Kura.Graph

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

section ext

lemma inc₂_eq_inc₂_iff_inc_eq_inc : G.Inc₂ e = G'.Inc₂ e ↔ G.Inc e = G'.Inc e := by
  constructor <;> rintro h
  · simp_rw [funext_iff, inc_iff_exists_inc₂, eq_iff_iff]
    exact fun x => exists_congr (fun y => by rw [h])
  · ext x y
    rw [inc₂_iff_inc_and_loop, inc₂_iff_inc_and_loop, isLoopAt_iff, isLoopAt_iff, h]

lemma inc_eq_inc_iff_incFun_eq_incFun : G.Inc e = G'.Inc e ↔ G.IncFun e = G'.IncFun e := by
  constructor <;> rintro h <;> ext x
  · obtain h0 | h1 | h2 := G'.incFun_eq_zero_or_one_or_two e x
    · rwa [h0, G.incFun_eq_zero, h, ← G'.incFun_eq_zero]
    · simp_rw [h1, G.incFun_eq_one_iff_isNonloopAt, isNonloopAt_iff, h, ← isNonloopAt_iff]
      rwa [← G'.incFun_eq_one_iff_isNonloopAt]
    simp_rw [h2, G.incFun_eq_two_iff_isLoopAt, isLoopAt_iff, h, ← isLoopAt_iff]
    rwa [← G'.incFun_eq_two_iff_isLoopAt]
  · rw [← incFun_ne_zero, h, incFun_ne_zero]

lemma incFun_eq_incFun_iff_toMultiset_eq_toMultiset :
    G.IncFun e = G'.IncFun e ↔ G.toMultiset e = G'.toMultiset e := by
  classical
  constructor <;> rintro h
  · have : ∀ v, G.IncFun e v = G'.IncFun e v := fun v ↦ by rw [h]
    simp_rw [← toMultiset_count] at this
    exact Multiset.ext.mpr this
  · ext v
    rw [← toMultiset_count, h, toMultiset_count]

lemma toSym2_eq_toSym2_iff_inc₂_eq_inc₂ (he : e ∈ G.E) (he' : e ∈ G'.E) :
    G.toSym2 e he = G'.toSym2 e he' ↔ G.Inc₂ e = G'.Inc₂ e := by
  obtain ⟨x, y, hxy⟩ := G.exists_vx_inc₂ he
  obtain ⟨x', y', hx'y'⟩ := G'.exists_vx_inc₂ he'
  rw [(toSym2.eq_iff_inc₂ he).mpr hxy, (toSym2.eq_iff_inc₂ he').mpr hx'y']
  constructor <;> rintro h
  · ext u v
    rw [hxy.sym2_eq_iff, h, hx'y'.sym2_eq_iff]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (h ▸ hxy).eq_of_inc₂ hx'y'
    · rfl
    · exact Sym2.eq_swap

lemma edge_subset_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) : G.E ⊆ G'.E := by
  rintro e he
  obtain ⟨x, y, hbtw⟩ := Inc₂.exists_vx_inc₂ he
  exact (h e x y hbtw).edge_mem

lemma inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ (he : e ∈ G.E) (h : G.Inc₂ ≤ G'.Inc₂) :
    G.Inc₂ e = G'.Inc₂ e := by
  refine le_antisymm (h e) fun x y hinc₂ ↦ ?_
  obtain ⟨u, v, hbtw⟩ := Inc₂.exists_vx_inc₂ he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (h e u v hbtw).eq_of_inc₂ hinc₂
  · exact hbtw
  · exact Inc₂.comm.mp hbtw

lemma ext_inc₂ (hV : G.V = G'.V) (h : ∀ e x y, G.Inc₂ e x y ↔ G'.Inc₂ e x y) : G = G' := by
  ext e x y
  · rw [hV]
  · constructor <;> rintro H
    · obtain ⟨x, y, hbtw⟩ := Inc₂.exists_vx_inc₂ H
      rw [h] at hbtw
      exact hbtw.edge_mem
    · obtain ⟨x, y, hbtw⟩ := Inc₂.exists_vx_inc₂ H
      rw [← h] at hbtw
      exact hbtw.edge_mem
  · exact h e x y

lemma ext_inc₂_le (hV : G.V = G'.V) (hE : G'.E ⊆ G.E) (h : G.Inc₂ ≤ G'.Inc₂) : G = G' := by
  refine ext_inc₂ hV (fun e x y ↦ ⟨fun a ↦ h e x y a, fun hinc₂ ↦ ?_⟩)
  exact (inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ (hE hinc₂.edge_mem) h) ▸ hinc₂

/-- Two graphs with the same incidences are the same. -/
lemma ext_inc (hV : G.V = G'.V) (h : ∀ e x, G.Inc e x ↔ G'.Inc e x) : G = G' := by
  refine ext_inc₂ hV ?_
  intro e x y
  rw [inc₂_eq_inc₂_iff_inc_eq_inc.mpr (by ext x; exact h e x)]

lemma ext_incFun (hV : G.V = G'.V) (h : ∀ e, G.IncFun e = G'.IncFun e) : G = G' := by
  refine ext_inc hV ?_
  intro e x
  rw [inc_eq_inc_iff_incFun_eq_incFun.mpr (h e)]

lemma ext_toMultiset (hV : G.V = G'.V) (h : ∀ e, G.toMultiset e = G'.toMultiset e) : G = G' := by
  refine ext_incFun hV ?_
  intro e
  rw [incFun_eq_incFun_iff_toMultiset_eq_toMultiset.mpr (h e)]

lemma ext_toSym2 (hV : G.V = G'.V) (hE : G.E = G'.E)
    (h : ∀ e he he', G.toSym2 e he = G'.toSym2 e he') : G = G' := by
  refine ext_inc₂ hV ?_
  intro e x y
  by_cases he : e ∈ G.E <;> by_cases he' : e ∈ G'.E
  · specialize h e he he'
    rw [toSym2_eq_toSym2_iff_inc₂_eq_inc₂ he he'] at h
    rw [h]
  · exact he' (hE ▸ he) |>.elim
  · exact he (hE ▸ he') |>.elim
  · simp [he, he']
end ext

section intro

def ofInc₂ (V : Set α) (isBtw : β → α → α → Prop) (hsymm : ∀ e x y, isBtw e x y → isBtw e y x)
    (vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V)
    (eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    Graph α β where
  V := V
  E := {e | ∃ x y, isBtw e x y}
  Inc₂ e x y := isBtw e x y
  symm := hsymm
  vx_mem_left := vx_mem_of_isBtw_left
  edge_mem e x y hbtw := by use x, y
  exists_vx_inc₂ e he := mem_setOf_eq.mp he
  eq_of_inc₂ := eq_of_isBtw

variable {V : Set α} {isBtw : β → α → α → Prop} {h1 : ∀ e x y, isBtw e x y → isBtw e y x}
    {h2 : ∀ e x y, isBtw e x y → x ∈ V}
    {h3 : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)}

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
  eq_of_inc₂ a b c d e h1 h2 := by
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
  eq_of_inc₂ a b c d e h1 h2 := by
    simp only at h1 h2
    rwa [h1, Multiset.pair_eq_pair_iff] at h2

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


def ofIncFun (V : Set α) (incFun : β → α →₀ ℕ) (vx_mem : ∀ e v, incFun e v ≠ 0 → v ∈ V)
    : Graph α β where
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
  edge_mem e x y hbtw := by
    simp [← hbtw]
  exists_vx_inc₂ e he := by
    classical
    simp only
    have : (incFun e).toMultiset.card = 2 := by simpa
    rw [Multiset.card_eq_two] at this
    obtain ⟨x, y, hxy⟩ := this
    use x, y
    rw [← hxy, Finsupp.toMultiset_toFinsupp]
  eq_of_inc₂ a b c d e h1 h2 := by
    simp only at h1 h2
    rwa [← h2, EmbeddingLike.apply_eq_iff_eq, Multiset.pair_eq_pair_iff] at h1

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
  eq_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨he, h1⟩ := h1
    obtain ⟨he', h2⟩ := h2
    simpa [h1] using h2

variable {E : Set β} {tosym2 : ∀ (e) (_he : e ∈ E), Sym2 α} {vx_mem : ∀ e v he, v ∈ tosym2 e he → v ∈ V}

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

section SubgraphOrder
/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ≤ G₂.V ∧ G₁.Inc₂ ≤ G₂.Inc₂
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃S⟩ := h₂₃
    exact ⟨h₁₂v.trans h₂₃v, h₁₂S.trans h₂₃S⟩
  le_antisymm G₁ G₂ h₁₂ h₂₁ := ext_inc₂ (h₁₂.1.antisymm h₂₁.1) fun e x y ↦ (by
    rw [h₁₂.2.antisymm h₂₁.2])

@[simp] lemma vx_subset_of_le (hle : G ≤ H) : G.V ⊆ H.V := hle.1

@[simp] lemma mem_of_le (hle : G ≤ H) : x ∈ G.V → x ∈ H.V := (hle.1 ·)

@[simp] lemma edge_subset_of_le (hle : G ≤ H) : G.E ⊆ H.E := edge_subset_of_inc₂_le_inc₂ hle.2

@[simp] lemma edge_mem_of_le (hle : G ≤ H) : e ∈ G.E → e ∈ H.E := (edge_subset_of_le hle ·)

lemma Inc_eq_Inc_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc e = H.Inc e := by
  rw [← inc₂_eq_inc₂_iff_inc_eq_inc]
  exact inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ he hle.2

lemma incFun_eq_incFun_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.IncFun e = H.IncFun e := by
  rw [← inc_eq_inc_iff_incFun_eq_incFun]
  exact Inc_eq_Inc_of_le hle he

lemma Inc₂_eq_Inc₂_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc₂ e = H.Inc₂ e := by
  rw [inc₂_eq_inc₂_iff_inc_eq_inc]
  exact Inc_eq_Inc_of_le hle he

lemma le_of_exist_mutual_le (hle1 : G' ≤ H') (hle2 : H ≤ H') : G' ≤ H ↔ G'.V ⊆ H.V ∧ G'.E ⊆ H.E := by
  constructor
  · intro h
    exact ⟨vx_subset_of_le h, edge_subset_of_le h⟩
  · rintro ⟨hV, hE⟩
    refine ⟨hV, ?_⟩
    rintro e x y hbtw
    rwa [Inc₂_eq_Inc₂_of_le hle2 (hE hbtw.edge_mem), ← Inc₂_eq_Inc₂_of_le hle1 hbtw.edge_mem]

-- This is now the definition of `le`
lemma le_iff_inc₂ : G ≤ H ↔ G.V ⊆ H.V ∧ G.Inc₂ ≤ H.Inc₂ := Iff.rfl

@[simp]
lemma Inc₂.le (hle : G ≤ H) (h : G.Inc₂ e u v) : H.Inc₂ e u v := by
  rwa [← Inc₂_eq_Inc₂_of_le hle (edge_mem h)]

lemma Inc₂.le_of_le (hle : G ≤ H) : G.Inc₂ ≤ H.Inc₂ := hle.2

@[simp]
lemma Inc.le (hle : G ≤ H) (hinc : G.Inc e x) : H.Inc e x := by
  rwa [← Inc_eq_Inc_of_le hle hinc.edge_mem]

lemma Inc.le_of_le (hle : G ≤ H) : G.Inc ≤ H.Inc := by
  rintro e x ⟨y, hbtw⟩
  use y, hbtw.le hle

lemma IsLoopAt_iff_IsLoopAt_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.IsLoopAt e x ↔ H.IsLoopAt e x := by
  rw [← inc₂_eq_iff_isLoopAt, ← inc₂_eq_iff_isLoopAt]
  rw [Inc₂_eq_Inc₂_of_le hle he]

lemma IsLoopAt.le (hisLoopAt : G.IsLoopAt e x) (hle : G ≤ H) : H.IsLoopAt e x := by
  rwa [← IsLoopAt_iff_IsLoopAt_of_edge_mem_le hle hisLoopAt.edge_mem]

lemma IsNonloopAt_iff_IsNonloopAt_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.IsNonloopAt e x ↔ H.IsNonloopAt e x := by
  rw [← inc_and_not_isLoopAt_iff_isNonloopAt, ← inc_and_not_isLoopAt_iff_isNonloopAt]
  refine Iff.and ?_ ?_
  · rw [Inc_eq_Inc_of_le hle he]
  · rw [IsLoopAt_iff_IsLoopAt_of_edge_mem_le hle he]

lemma IsNonloopAt.le (hisNonloopAt : G.IsNonloopAt e x) (hle : G ≤ H) : H.IsNonloopAt e x := by
  rwa [← IsNonloopAt_iff_IsNonloopAt_of_edge_mem_le hle hisNonloopAt.edge_mem]

lemma Adj.le (hle : G ≤ H) (hadj : G.Adj x y) : H.Adj x y := by
  obtain ⟨e, hbtw⟩ := hadj
  use e
  exact hbtw.le hle

lemma le_iff_inc : G ≤ H ↔ G.V ⊆ H.V ∧ G.E ⊆ H.E ∧ ∀ e ∈ G.E, ∀ v,
  G.Inc e v ↔ H.Inc e v := by
  constructor
  · rintro hle
    exact ⟨vx_subset_of_le hle, edge_subset_of_le hle, fun e he v ↦ by rw [Inc_eq_Inc_of_le hle he]⟩
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, fun e x y ↦ ?_⟩
    by_cases he : e ∈ G.E
    · rw [inc₂_eq_inc₂_iff_inc_eq_inc.mpr (by ext; exact hinc e he _)]
    · simp [he]

/-- If G₁ ≤ G₂ and G₂ is finite, then G₁ is finite too. -/
theorem finite_of_le_finite (hle : G ≤ H) [h : H.Finite] : G.Finite := by
  constructor
  · -- Prove the vertex set is finite
    apply Set.Finite.subset h.vx_fin
    exact vx_subset_of_le hle
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    exact edge_subset_of_le hle

lemma vx_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.V.ncard ≤ H.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le hle) hfin.vx_fin

lemma edge_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.E.ncard ≤ H.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le hle) hfin.edge_fin

end SubgraphOrder

section Degree

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, (G.IncFun e v : ℕ∞)

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

def regular (G : Graph α β) := ∃ d, ∀ v, G.degree v = d

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.IncFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_finsum [Finite β] (G : Graph α β) (v : α) :
    G.degree v = ∑ᶠ e, G.IncFun e v := by
  have := Fintype.ofFinite β
  rw [degree_eq_fintype_sum, finsum_eq_sum_of_fintype]

@[simp]
lemma finsum_incFun_eq (he : e ∈ G.E) : ∑ᶠ v, G.IncFun e v = 2 := by
  simp_rw [← IncFun.sum_eq he, Finsupp.sum, id_eq]
  rw [finsum_eq_finset_sum_of_support_subset]
  simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) :
    ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.IncFun e v) G.E.toFinite (Set.finite_univ (α := α))
  convert h.symm using 1
  · simp only [Set.mem_univ, finsum_true, degree_eq_finsum, finsum_mem_def]
    convert rfl with v e
    simp only [Set.indicator_apply_eq_self, incFun_eq_zero, not_imp_not]
    apply Inc.edge_mem
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show G.E = G.E from rfl) (fun x h ↦ finsum_incFun_eq h)]
  simp [mul_comm]

end Degree


section Connected

@[simp]
def reflAdj (G : Graph α β) (x y : α) :=
  G.Adj x y ∨ x = y ∧ x ∈ G.V

lemma reflAdj.of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
  simp only [reflAdj, h, and_self, or_true]

@[simp]
lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj.of_vxMem h

lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
  apply h.imp
  · exact fun h ↦ h.symm
  · rintro ⟨rfl, hx⟩
    exact ⟨rfl, hx⟩

lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
  refine ⟨reflAdj.symm, reflAdj.symm⟩

lemma Inc.reflAdj_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.reflAdj x y := by
  by_cases hxy : x = y
  · subst y
    right
    exact ⟨rfl, hx.vx_mem⟩
  · left
    use e
    rw [inc₂_iff_inc_and_loop]
    use hx, hy, fun h ↦ (hxy h).elim

@[simp]
lemma reflAdj.mem_left (h : G.reflAdj x y) : x ∈ G.V := by
  apply h.elim
  · exact fun a ↦ a.mem_left
  · tauto

@[simp]
lemma reflAdj.mem_right (h : G.reflAdj x y) : y ∈ G.V := by
  rw [reflAdj.comm] at h
  exact h.mem_left

@[simp]
lemma Inc₂.reflAdj (h : G.Inc₂ e x y) : G.reflAdj x y := by
  left
  use e

@[simp]
lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
  left
  exact h

lemma reflAdj.Adj_of_ne (h : G.reflAdj x y) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨e, h⟩ | ⟨rfl, hx⟩ := h
  · use e
  · contradiction

@[simp]
lemma reflAdj.Adj_iff_ne (hne : x ≠ y) : G.reflAdj x y ↔ G.Adj x y :=
  ⟨fun h => h.Adj_of_ne hne, fun h => h.reflAdj⟩

lemma reflAdj.le (h : G.reflAdj u v) (hle : G ≤ H) : H.reflAdj u v := by
  obtain hadj | ⟨rfl, hu⟩ := h
  · left
    exact hadj.le hle
  · right
    simp only [vx_subset_of_le hle hu, and_self]


def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

@[simp]
lemma Inc₂.connected (h : G.Inc₂ e x y) : G.Connected x y :=
  Relation.TransGen.single h.reflAdj

@[simp]
lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

@[simp]
lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| reflAdj.of_vxMem hx

lemma Inc.connected_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.Connected x y :=
  reflAdj.connected (hx.reflAdj_of_inc hy)

lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  rw [Relation.transGen_swap]
  congr! 1
  ext
  exact reflAdj.comm

@[simp]
lemma Connected.refl (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

@[simp]
lemma Connected.exists_connected (hx : x ∈ G.V) : ∃ y, G.Connected x y := by
  use x, Connected.refl hx

lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
  rwa [Connected.comm]

instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

lemma Connected.trans (hxy : G.Connected x y) (hyz : G.Connected y z) :
    G.Connected x z := Relation.TransGen.trans hxy hyz

instance : IsTrans α (G.Connected) := ⟨fun _ _ _ ↦ Connected.trans⟩

@[simp]
lemma Connected.mem_left (hconn : G.Connected x y) : x ∈ G.V := by
  simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
  obtain ⟨a, hradj, hTG⟩ := hconn
  exact hradj.mem_left

@[simp]
lemma Connected.mem_right (hconn : G.Connected x y) : y ∈ G.V := by
  rw [Connected.comm] at hconn
  exact hconn.mem_left

@[simp]
lemma not_connected_of_not_mem (h : x ∉ G.V) : ¬G.Connected x y := by
  contrapose! h
  exact h.mem_left

@[simp]
lemma not_connected_of_not_mem' (h : y ∉ G.V) : ¬G.Connected x y := by
  rw [Connected.comm]
  exact not_connected_of_not_mem h

@[simp]
lemma Connected.refl_iff : G.Connected x x ↔ x ∈ G.V := by
  refine ⟨?_, Connected.refl⟩
  rintro h
  exact h.mem_left

lemma Connected.le (h : G.Connected u v) (hle : G ≤ H) : H.Connected u v := by
  induction h with
  | single huv => exact Relation.TransGen.single (huv.le hle)
  | tail huv h ih => exact Relation.TransGen.tail ih (h.le hle)

class Conn (G : Graph α β) : Prop where
  all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y

open Partition

def ConnectedPartition (G : Graph α β) : Partition (Set α) := Partition.ofRel (G.Connected)

def Component (G : Graph α β) (v : α) := {u | G.Connected v u}

def ComponentSets (G : Graph α β) (V : Set α) := {Component G u | u ∈ V}

@[simp]
lemma ComponentPartition.supp : G.ConnectedPartition.supp = G.V := by
  simp [ConnectedPartition]

@[simp]
lemma set_spec_connected_comm : {x | G.Connected x y} = {x | G.Connected y x} := by
  simp_rw [Connected.comm]

@[simp] lemma set_spec_connected_eq_componentSet : {x | G.Connected y x} = G.Component y := rfl

@[simp]
lemma Component.empty : G.Component x = ∅ ↔ x ∉ G.V := by
  constructor
  · intro h hx
    rw [← mem_empty_iff_false, ← h]
    exact Connected.refl hx
  · intro h
    ext y
    simp [Component, h]

@[simp]
lemma Component.eq (hx : x ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y :=
  (rel_iff_eqv_class_eq_left (Connected.refl hx)).symm

@[simp]
lemma Component.eq' (hy : y ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y := by
  rw [eq_comm, Connected.comm, eq hy]

@[simp]
lemma Component.mem_partition : G.Component x ∈ G.ConnectedPartition ↔ x ∈ G.V := by
  refine mem_ofRel_iff.trans ?_
  simp +contextual only [Connected.refl_iff, set_spec_connected_eq_componentSet, iff_def,
    forall_exists_index, and_imp, eq', eq]
  refine ⟨fun y hy hconn ↦ hconn.mem_left, fun h ↦ ?_⟩
  use x, h, Connected.refl h

@[simp] lemma Component.mem : y ∈ G.Component x ↔ G.Connected x y := by rfl

lemma Component.mem' : y ∈ G.Component x ↔ G.Connected y x := by
  rw [Connected.comm, Component.mem]

-- @[simp] lemma ComponentSet.self_mem : x ∈ G.ComponentSet x ↔ x ∈ G.V := by simp

@[simp]
lemma ComponentSets.mem (hx : x ∈ G.V) :
    G.Component x ∈ G.ComponentSets T ↔ ∃ y ∈ T, G.Connected x y := by
  simp only [ComponentSets, mem_setOf_eq, hx, Component.eq']
  simp_rw [Connected.comm]

lemma ComponentSets.componentSet (hx : x ∈ G.V) :
    G.ComponentSets (G.Component x) = {G.Component x} := by
  ext S
  simp +contextual only [mem_singleton_iff, iff_def, hx, mem, Component.mem, and_self,
    Connected.exists_connected, implies_true, and_true]
  rintro ⟨y, hy, rfl⟩
  simpa [hx, Connected.comm] using hy

lemma ConnectedPartition.le (hle : G ≤ H) : G.ConnectedPartition ≤ H.ConnectedPartition := by
  simpa [ConnectedPartition] using fun u v ↦ (Connected.le · hle)

@[simp]
lemma ConnectedPartition.Rel : G.ConnectedPartition.Rel = G.Connected := by
  unfold ConnectedPartition
  rw [rel_ofRel_eq]

def SetConnected (G : Graph α β) (S T : Set α) : Prop := ∃ s ∈ S, ∃ t ∈ T, G.Connected s t

namespace SetConnected
variable {G : Graph α β} {S S' T T' U V : Set α}

lemma refl (h : ∃ x ∈ S, x ∈ G.V) : G.SetConnected S S := by
  obtain ⟨x, hxS, hxV⟩ := h
  use x, hxS, x, hxS, Connected.refl hxV

lemma symm (h : G.SetConnected S T) : G.SetConnected T S := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨t, ht, s, hs, h.symm⟩

lemma comm : G.SetConnected S T ↔ G.SetConnected T S := ⟨SetConnected.symm, SetConnected.symm⟩

lemma left_subset (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hS hs, t, ht

lemma right_subset (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
  rw [SetConnected.comm] at h ⊢
  exact h.left_subset hT

lemma subset (h : G.SetConnected S T) (hS : S ⊆ S') (hT : T ⊆ T') : G.SetConnected S' T' :=
  (h.left_subset hS).right_subset hT

lemma left_supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) T := by
  constructor
  · rintro ⟨s, hsS, t, htT, h⟩
    use s, ⟨hsS, h.mem_left⟩, t, htT
  · rintro ⟨s, ⟨hsS, hs⟩, t, htT, h⟩
    use s, hsS, t, htT

lemma right_supported : G.SetConnected S T ↔ G.SetConnected S (T ∩ G.V) := by
  rw [comm, left_supported, comm]

lemma supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) (T ∩ G.V) := by
  rw [left_supported, right_supported]

lemma le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨s, hs, t, ht, h.le hle⟩

@[simp]
lemma empty_source : ¬ G.SetConnected ∅ T := by
  rintro ⟨s, hs, t, ht, h⟩
  simp at hs

@[simp]
lemma empty_target : ¬ G.SetConnected S ∅ := by
  rw [SetConnected.comm]
  exact empty_source

@[simp]
lemma nonempty_inter (h : (S ∩ T ∩ G.V).Nonempty) : G.SetConnected S T := by
  obtain ⟨x, ⟨hxS, hxT⟩, hx⟩ := h
  use x, hxS, x, hxT, Connected.refl hx

lemma exists_mem_left (h : G.SetConnected S T) : ∃ x ∈ S, x ∈ G.V := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨s, hs, h.mem_left⟩

lemma exists_mem_right (h : G.SetConnected S T) : ∃ x ∈ T, x ∈ G.V := by
  rw [SetConnected.comm] at h
  exact exists_mem_left h

end SetConnected
