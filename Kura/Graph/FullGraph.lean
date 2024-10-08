import Kura.Graph.Defs


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) [fullGraph G] (e : E) (u v w : V)


@[simp]
lemma not_dir_none_none : G.inc e ≠ dir (none, none) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this


@[simp]
lemma not_dir_some_none : G.inc e ≠ dir (some u, none) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this

@[simp]
lemma not_dir_none_some : G.inc e ≠ dir (none, some u) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this

@[simp]
lemma endAt_card_two : Multiset.card (G.endAt e) = 2 := by
  match h : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp_all
  | undir s => simp only [endAt, edge.endAt, h, Sym2.toMultiset_card]

lemma exist_two_mem : ∃ u v, u ∈ G.inc e ∧ v ∈ G.inc e := by
  obtain ⟨u, v, h⟩ := Multiset.card_eq_two.mp (endAt_card_two G e)
  refine ⟨u, v, ?_, ?_⟩ <;> simp only [instedgeMem, h, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton, true_or, or_true]

@[simp]
lemma gofrom?_isSome_iff_mem_startAt (v : V) (e : E) :
    (G.gofrom? v e).isSome ↔ v ∈ G.startAt e := by
  simp [startAt, edge.startAt, gofrom?, edge.gofrom?]
  match he : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp_all ; rw [Eq.comm]
  | undir s => simp only [Option.isSome_dite, Sym2.mem_toMultiset_iff]

theorem exist (G : Graph V E) [fullGraph G] : IsEmpty E ∨ Nonempty V := by
  by_cases hE : IsEmpty E
  · exact Or.inl hE
  · simp at hE
    choose v _ using exist_two_mem G (@Classical.ofNonempty _ hE)
    exact Or.inr (Nonempty.intro v)

end Graph
