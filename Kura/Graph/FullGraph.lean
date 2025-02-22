import Kura.Graph.Defs


namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) [FullGraph G] (e : E) (u v w : V)


@[simp]
lemma not_dir_none_none : G.inc e ≠ dir (none, none) := by
  intro h
  have := FullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this


@[simp]
lemma not_dir_some_none : G.inc e ≠ dir (some u, none) := by
  intro h
  have := FullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this

@[simp]
lemma not_dir_none_some : G.inc e ≠ dir (none, some u) := by
  intro h
  have := FullGraph.all_full (G := G) e
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
lemma gofrom?_isSome_iff_mem_startAt [DecidableEq V] (v : V) (e : E) :
    (G.gofrom? v e).isSome ↔ v ∈ G.startAt e := by
  simp [startAt, edge.startAt, gofrom?, edge.gofrom?]
  match he : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp_all ; rw [Eq.comm]
  | undir s => simp only [Option.isSome_dite, Sym2.mem_toMultiset_iff]

theorem exist (G : Graph V E) [FullGraph G] : IsEmpty E ∨ Nonempty V := by
  by_cases hE : IsEmpty E
  · exact Or.inl hE
  · simp at hE
    choose v _ using exist_two_mem G (@Classical.ofNonempty _ hE)
    exact Or.inr (Nonempty.intro v)

lemma NonemptyV_of_e (G : Graph V E) [FullGraph G] (e : E) : Nonempty V := by
  obtain h | h := G.exist
  · exfalso
    exact IsEmpty.false e
  · assumption

noncomputable def v1 : V := (G.inc e).v1 (G.all_full e)

noncomputable def v2 : V := (G.inc e).v2 (G.all_full e)

@[simp↓ 101]
lemma dir_v1 {e} {u v} (h : G.inc e = dir (some u, some v)) : v1 G e = u := by
  unfold v1
  simp only [h, edge.dir_v1]

@[simp↓ 101]
lemma dir_v2 {e} {u v} (h : G.inc e = dir (some u, some v)) : v2 G e = v := by
  unfold v2
  simp only [h, edge.dir_v2]

@[simp↓ 101]
lemma isLoop_iff_v1_eq_v2 : G.isLoop e ↔ v1 G e = v2 G e := by
  match h : G.inc e with
  | dir (a, b) =>
    cases a <;> cases b
    · simp only [not_dir_none_none] at h
    · simp only [not_dir_none_some] at h
    · simp only [not_dir_some_none] at h
    · rw [G.dir_v1 h, G.dir_v2 h]
      simp only [isLoop, h, dir_isLoop_iff]
  | undir s => simp only [isLoop, edge.isLoop, h, Sym2.isDiag_iff_out_fst_eq_out_snd, v1, undir_v1,
    v2, undir_v2]

lemma canGo_v1_v2 [DecidableEq V] : G.canGo (G.v1 e) e (G.v2 e) := edge.canGo_v1_v2 _

@[simp]
lemma adj_v12 [DecidableEq V] : G.adj (G.v1 e) (G.v2 e) := by
  use e
  exact canGo_v1_v2 G e

lemma v1_mem : v1 G e ∈ G.inc e := (G.inc e).v1_mem (G.all_full e)

lemma v2_mem : v2 G e ∈ G.inc e := (G.inc e).v2_mem (G.all_full e)

end Graph
