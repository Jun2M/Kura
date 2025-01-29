import Kura.Connectivity.Walk

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E)


structure Closed extends Walk G where
  startFinish : toWalk.start = toWalk.finish

@[ext, simp]
lemma Closed.ext (c1 c2 : G.Closed) : c1.toWalk = c2.toWalk → c1 = c2 := by
  intro h
  cases c1
  cases c2
  simp_all only

namespace Closed

@[simp]
def ofLoop (e : E) (he : G.isLoop e) : G.Closed where
  toWalk := Walk.some (G.ofIsLoop he) e (G.ofIsLoop he) (canGo_ofIsLoop he)
  startFinish := by simp only [Walk.some, Walk.finish, List.getLast_singleton]

lemma isLoop_of_length_one {C : G.Closed} (hC : C.length = 1) (hedge : C.edges ≠ []) :
    G.isLoop (C.edges.head hedge) := by
  rw [Walk.length, List.length_eq_one] at hC
  obtain ⟨⟨u, e, v⟩, hstep⟩ := hC
  apply isLoop_of_canGo_self
  use C.start
  convert C.step_spec (C.steps.head ?_) (List.head_mem _)
  · refine C.start_spec ?_
  · simp only [Walk.edges, List.head_map]
  · rw [C.startFinish, ← Walk.vertices_getLast_eq_finish]
    simp only [Walk.vertices, hstep, List.map_cons, List.map_nil, ne_eq, List.cons_ne_self,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton, List.head_cons]
  · simp only [hstep, ne_eq, List.cons_ne_self, not_false_eq_true]

variable {G}

/-- ClosedWalk has some start point by the definition. rotate it. -/
def rotate (C : G.Closed) (n : ℕ) : G.Closed where
  start := match hsteps : C.steps with
    | [] => C.start
    | _ :: _ => ((C.steps.rotate n).head
      (List.rotate_eq_nil_iff.not.mpr (hsteps ▸ List.cons_ne_nil _ _))).fst
  steps := C.steps.rotate n
  start_spec h := by
    simp at h
    split
    · absurd h
      assumption
    · simp only
  step_spec uev he := by
    simp only [List.mem_rotate] at he
    exact C.step_spec uev he
  next_step := by
    refine C.next_step.rotate _ ?_
    rintro x hx y hy
    obtain ⟨hnil, rfl⟩ := List.mem_getLast?_eq_getLast hx
    obtain ⟨_hnil', rfl⟩ := List.mem_head?_eq_head hy
    rw [← C.steps.getLast_map (·.2.2), ← C.steps.head_map (·.1), eq_comm]
    convert C.startFinish
    · convert C.start_spec hnil |>.symm
      refine List.head_map (fun x ↦ x.1) C.steps ?_
    · convert C.steps_getLast_ssnd_eq_finish hnil |>.symm
      refine List.getLast_map (fun x ↦ x.2.2) C.steps ?_
    all_goals simp only [ne_eq, List.map_eq_nil_iff, hnil, not_false_eq_true]
  startFinish := sorry

@[simp]
lemma rotate_edges (C : G.Closed) (n : ℕ) : (C.rotate n).edges = C.edges.rotate n := by
  simp only [Walk.edges, rotate, List.map_rotate]

/-- Pick a vertex, v, in a ClosedWalk. Get a walk from v to v along the ClosedWalk -/
def cut (C : G.Closed) {v : V} (_ : v ∈ C.vertices) : G.Walk :=
  let i := C.vertices.indexOf v
  (C.rotate i).toWalk

/-- Pick 2 vertices, u & v, in a ClosedWalk. Get edge-disjoint paths u to v and v to u -/
def split (C : G.Closed) {u v : V} (hu : u ∈ C.vertices) (hv : v ∈ C.vertices) : G.Path × G.Path :=
  sorry

end Closed

structure Cycle extends Closed G where
  vNodup' : toWalk.vertices.tail.Nodup
  eNodup' : toWalk.edges.Nodup
  eNonempty : toWalk.edges ≠ []

namespace Cycle

@[ext, simp]
lemma ext (C1 C2 : G.Cycle) : C1.toWalk = C2.toWalk → C1 = C2 := by
  intro h
  rcases C1 with ⟨⟨w, hw⟩, hnodup⟩
  rcases C2 with ⟨⟨w', hw'⟩, hnodup'⟩
  simpa using h

instance instPreorder : Preorder (Cycle G) where
  le := λ c₁ c₂ => c₁.toWalk.length ≤ c₂.toWalk.length
  le_refl := λ c => Nat.le_refl _
  le_trans := λ c₁ c₂ c₃ => Nat.le_trans

instance DecEq [DecidableEq E] : DecidableEq G.Cycle := by
  intro C1 C2
  refine @decidable_of_decidable_of_iff (C1.toWalk = C2.toWalk) (C1 = C2) ?_ ?_
  infer_instance
  rw [Cycle.ext_iff]

instance instFintype [Fintype E] [DecidableEq E] : Fintype (Cycle G) where
  elems := by
    -- exact (Finset.univ : Finset E)
    --   |>.image Walk.nil
    --   |>.image Walk.extensions
    sorry
  complete := sorry

def ofLoop (e : E) (he : G.isLoop e) : G.Cycle where
  toClosed := Closed.ofLoop G e he
  vNodup' := by simp only [Walk.vertices, Closed.ofLoop, Walk.some, List.map_cons, List.map_nil,
    List.tail_cons, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  eNodup' := by simp only [Closed.ofLoop, Walk.some_edges, List.nodup_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_self]
  eNonempty := by simp only [Closed.ofLoop, Walk.some_edges, ne_eq, List.cons_ne_self,
    not_false_eq_true]

lemma not_simple_of_length_two {C : G.Cycle} (hC : C.length = 2) : ¬ G.Simple := by
  rintro hSimple
  obtain hInj := hSimple.inc_inj
  rw [← Walk.edges_length, List.length_eq_two] at hC
  obtain ⟨e1, e2, H⟩ := hC
  specialize @hInj e1 e2 ?_
  · rw [inc_eq_get, inc_eq_get, undir.injEq]
    sorry
  subst e2
  exact List.not_nodup_pair _ (H ▸ C.eNodup')

variable {G}

/-- Cycle has some start point by the definition. rotate it. -/
def rotate (C : G.Cycle) (n : ℕ) : G.Cycle where
  toClosed := C.toClosed.rotate n
  vNodup' := by
    simp only [Walk.vertices, Closed.rotate, List.tail_cons, List.map_rotate, List.nodup_rotate]
    exact C.vNodup'
  eNodup' := by
    simp only [Walk.edges, Closed.rotate, List.map_rotate, List.nodup_rotate]
    exact C.eNodup'
  eNonempty := by
    simp only [Closed.rotate_edges, ne_eq, List.rotate_eq_nil_iff]
    exact C.eNonempty

/-- Pick a vertex, v, in a cycle. Get a walk from v to v along the cycle -/
def cut (C : G.Cycle) {v : V} (_ : v ∈ C.vertices) : G.Walk :=
  let i := C.vertices.indexOf v
  (C.rotate i).toWalk

/-- Pick 2 vertices, u & v, in a cycle. Get edge-disjoint paths u to v and v to u -/
def split (C : G.Cycle) {u v : V} (hu : u ∈ C.vertices) (hv : v ∈ C.vertices) : G.Path × G.Path :=
  sorry

lemma isLoop_of_edges_singleton (C : G.Cycle) (e : E) (he : C.edges = [e]) : G.isLoop e := by
  unfold Walk.edges at he
  have : C.steps = [(C.start, e, C.finish)] := by
    sorry
  rw [← C.startFinish] at this
  refine isLoop_of_canGo_self (G.inc e) ⟨ C.start, ?_ ⟩
  exact C.step_spec (C.start, e, C.start) (by rw [this]; exact List.mem_singleton_self _)


end Cycle

namespace Emb

def cycle {G : Graph V E} {H : Graph W F} (A : G ⊆ᴳ H) (C : G.Cycle) : H.Cycle where
  toWalk := A.walk C.toWalk
  startFinish := by
    simp only [walk_start, walk_finish, C.startFinish]
  vNodup' := by
    simp only [walk_vertices]
    exact C.vNodup'.map A.fᵥinj
  eNodup' := by
    simp only [walk_edges]
    exact (List.nodup_map_iff_inj_on C.eNodup').mpr (fun _ _ _ _ hxy ↦ A.fₑinj hxy)
  eNonempty := by
    simp only [walk_edges, ne_eq, List.map_eq_nil_iff]
    exact C.eNonempty

@[simp]
lemma cycle_start {G : Graph V E} {H : Graph W F} (A : G ⊆ᴳ H) (C : G.Cycle) :
    (A.cycle C).start = A.fᵥ C.start := by simp only [cycle, walk_start]

@[simp]
lemma cycle_finish {G : Graph V E} {H : Graph W F} (A : G ⊆ᴳ H) (C : G.Cycle) :
    (A.cycle C).finish = A.fᵥ C.finish := by simp only [cycle, walk_finish]

@[simp]
lemma cycle_vertices {G : Graph V E} {H : Graph W F} (A : G ⊆ᴳ H) (C : G.Cycle) :
    (A.cycle C).vertices = C.vertices.map A.fᵥ := by simp only [cycle, walk_vertices]

@[simp]
lemma cycle_edges {G : Graph V E} {H : Graph W F} (A : G ⊆ᴳ H) (C : G.Cycle) :
    (A.cycle C).edges = C.edges.map A.fₑ := by simp only [cycle, walk_edges]

end Emb


-- def IsVertexCycle (v : V) (c : G.Cycle) : Prop :=
--   @Minimal _ {le:=fun c1 c2 => (c1 : G.Cycle).toWalk.length ≤ (c2 : G.Cycle).toWalk.length} (∀ u ∈ G.neighbourhood v, u ∈ ·.vertices) c


structure Tour extends Closed G, Trail G
