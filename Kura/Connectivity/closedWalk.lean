import Kura.Connectivity.Walk
import Init.Data.List.Nat.TakeDrop
import Kura.Graph.Separation
namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E)


structure Closed extends Walk G where
  startFinish : toWalk.start = toWalk.finish
  stepsNeNil : toWalk.steps ≠ []

@[ext, simp]
lemma Closed.ext (c1 c2 : G.Closed) : c1.toWalk = c2.toWalk → c1 = c2 := by
  intro h
  cases c1
  cases c2
  simp_all only

namespace Closed

variable {G}

instance instLengthNeZero {C : G.Closed} : NeZero C.length where
  out h := C.stepsNeNil (List.eq_nil_of_length_eq_zero h)

lemma vertices_tail_eq_vertices_dropLast_rotate {C : G.Closed} :
    C.vertices.tail = (C.vertices.dropLast.rotate 1) := by
  by_cases h : C.steps = []
  · simp only [Walk.vertices, h, List.map_nil, List.tail_cons, List.dropLast_single,
    List.rotate_nil]
  · simp only [Walk.vertices, List.tail_cons]
    rw [List.dropLast_cons_of_ne_nil, List.rotate_cons_succ, List.rotate_zero, eq_comm]
    convert (List.map (fun x ↦ x.2.2) C.steps).dropLast_concat_getLast ?_
    rw [List.getLast_map, Walk.steps_getLast_ssnd_eq_finish]
    exact C.startFinish
    all_goals simpa only [ne_eq, List.map_eq_nil_iff]

@[simp]
lemma toWalk_ne_nil (C : G.Closed) : C.toWalk ≠ Walk.nil G C.start := by
  intro h
  apply C.stepsNeNil
  have := Walk.nil_steps G C.start
  rwa [← h] at this

lemma one_le_length (C : G.Closed) : 1 ≤ C.length := by
  by_contra! h
  simp only [Nat.lt_one_iff, Walk.length_zero_iff_eq_nil, toWalk_ne_nil] at h

@[simp]
lemma vertices_dropLast_ne_nil (C : G.Closed) : C.vertices.dropLast ≠ [] := by
  rw [← Walk.steps_fst_vertices]
  simp only [ne_eq, List.map_eq_nil_iff, C.stepsNeNil, not_false_eq_true]

@[simp]
lemma vertices_tail_ne_nil (C : G.Closed) : C.vertices.tail ≠ [] := by
  rw [← Walk.steps_ssnd_vertices]
  simp only [ne_eq, List.map_eq_nil_iff, C.stepsNeNil, not_false_eq_true]

@[simp]
def ofLoop (e : E) (he : G.isLoop e) : G.Closed where
  toWalk := Walk.some (G.ofIsLoop he) e (G.ofIsLoop he) (canGo_ofIsLoop he)
  startFinish := by
    simp only [Walk.some, Walk.finish, List.getLast_singleton, Walk.vertices, List.map_singleton]
    rfl
  stepsNeNil := by simp only [Walk.some, ne_eq, List.cons_ne_self, not_false_eq_true]

def ofWalkEndAdj (W : G.Walk) (e : E) (he : G.canGo W.finish e W.start) : G.Closed where
  toWalk := W.append (Walk.some W.finish e W.start he) (by simp only [Walk.finish, Walk.vertices,
    Walk.some])
  startFinish := by simp only [Walk.append_start, Walk.append_finish, Walk.some_finish]
  stepsNeNil := by simp only [Walk.append, Walk.some, ne_eq, List.append_eq_nil_iff,
    List.cons_ne_self, and_false, not_false_eq_true]

@[simp]
lemma ofWalkEndAdj_start (W : G.Walk) (e : E) (he : G.canGo W.finish e W.start) :
    (Closed.ofWalkEndAdj W e he).start = W.start := by simp only [ofWalkEndAdj, Walk.append_start]

@[simp]
lemma ofWalkEndAdj_finish (W : G.Walk) (e : E) (he : G.canGo W.finish e W.start) :
    (Closed.ofWalkEndAdj W e he).finish = W.start := by simp only [ofWalkEndAdj,
      Walk.append_finish, Walk.some_finish]

@[simp]
lemma ofWalkEndAdj_vertices (W : G.Walk) (e : E) (he : G.canGo W.finish e W.start) :
    (Closed.ofWalkEndAdj W e he).vertices = W.vertices ++ [W.start] := by
  simp only [ofWalkEndAdj, Walk.append_vertices, Walk.some_vertices, List.tail_cons]

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

lemma steps_getElem_ssnd_eq_vertices_getElem_add_one {C : G.Closed} {e : Fin C.length}
    (he : e.val < C.steps.length) (h : e.val + 1 < C.vertices.length) :
    C.steps[e.val].2.2 = C.vertices[(e + 1).val] := by
  by_cases h : e = Fin.last' C.length
  · subst e
    simp only [Fin.getElem_fin, Fin.val_last', Fin.last'_add_one_eq_zero, Fin.val_zero,
      List.getElem_zero, Walk.vertices_head_eq_start, C.startFinish]
    rw [← C.steps_getLast_ssnd_eq_finish C.stepsNeNil]
    congr
    apply C.steps.getElem_length_sub_one_eq_getLast
  · convert C.steps_getElem_snd_snd_eq_vertices_getElem_add_one e.val ?_ ?_
    rw [e.val_add_one']
    simp only [h, ↓reduceIte]
    · simp only [Fin.is_lt]
    · simp only [Walk.vertices_length, add_lt_add_iff_right, Fin.is_lt]

def exist_CycleGraph_Hom [Undirected G] (C : G.Closed):
    (CycleGraph C.length).Hom G where
  fᵥ v := by
    have hv : v.val < C.vertices.length := by
      rw [Walk.vertices_length]
      exact Nat.lt_add_right 1 v.prop
    exact C.vertices[v.val]
  fₑ e := by
    have he : e.val < C.edges.length := by
      rw [Walk.edges_length]
      exact e.prop
    exact C.edges[e.val]
  inc e := by
    simp only [C.inc_edges_getElem_eq_steps_fst_ssnd e.val, CycleGraph, map_undir, Sym2.map_pair_eq,
      undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    left
    refine ⟨C.steps_getElem_fst_eq_vertices_getElem _ _ _,
      steps_getElem_ssnd_eq_vertices_getElem_add_one e.prop ?_⟩
    simp only [Walk.vertices_length, add_lt_add_iff_right, Fin.is_lt]

-- def exist_CycleGraph_Hom [Undirected G] (C : G.Closed) (n : ℕ+) (hn : n.val = C.length):
--     (CycleGraph n).Hom G where
--   fᵥ v := by
--     have hv : v.val < C.vertices.length := by
--       simp only [Walk.vertices_length, ← hn]
--       omega
--     exact C.vertices[v.val]
--   fₑ e := by
--     have he : e.val < C.edges.length := by
--       simp only [Walk.edges_length, ← hn, Fin.is_lt]
--     exact C.edges[e.val]
--   inc e := by
--     simp only [C.inc_edges_getElem_eq_steps_fst_ssnd e.val, CycleGraph, map_undir, Sym2.map_pair_eq,
--       undir.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
--     left
--     refine ⟨C.steps_getElem_fst_eq_vertices_getElem _ _ _, ?_⟩
--     by_cases h : e = Fin.last' n
--     · subst e
--       simp only [Fin.val_last', hn, Fin.last'_add_one_eq_zero, Fin.val_zero, List.getElem_zero,
--         Walk.vertices_head_eq_start, C.startFinish]
--       rw [← C.steps_getLast_ssnd_eq_finish C.stepsNeNil]
--       congr
--       apply C.steps.getElem_length_sub_one_eq_getLast
--     · convert C.steps_getElem_snd_snd_eq_vertices_getElem_add_one e.val _ _
--       rw [e.val_add_one']
--       simp only [h, ↓reduceIte]
--       simp only [← hn, Fin.is_lt]
--       simp only [Walk.vertices_length, ← hn, add_lt_add_iff_right, Fin.is_lt]

/-- ClosedWalk has some start point by the definition. rotate it. -/
def rotate (C : G.Closed) (n : ℕ) : G.Closed where
  start := (C.vertices.dropLast.rotate n).head (by simp only [ne_eq, List.rotate_eq_nil_iff,
    vertices_dropLast_ne_nil, not_false_eq_true])
  steps := C.steps.rotate n
  start_spec h := by
    simp only [ne_eq, List.rotate_eq_nil_iff] at h
    simp_rw [← Walk.steps_fst_vertices, ← List.map_rotate, List.head_map]
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
    · rw [List.getLast_map]
      convert C.steps_getLast_ssnd_eq_finish hnil
      simpa only [ne_eq, List.map_eq_nil_iff]
    all_goals simp only [ne_eq, List.map_eq_nil_iff, hnil, not_false_eq_true]
  startFinish := by
    by_cases h : C.steps = []
    · simp only [h, List.rotate_nil, Walk.finish, Walk.vertices, List.map_nil,
      List.getLast_singleton]
    · simp [h, ← Walk.steps_fst_vertices, ← List.map_rotate, List.head_map]
      rw [← Walk.steps_getLast_ssnd_eq_finish _ (by simpa only [ne_eq, List.rotate_eq_nil_iff])]
      simp only
      nth_rw 1 [List.head_rotate h (Nat.mod_lt _ C.one_le_length)]
      rw [List.getLast_rotate h (Nat.mod_lt _ C.one_le_length), eq_comm]
      by_cases hmod : n % C.length = 0
      · simp only [Walk.step_length_eq_length, hmod, List.getElem_zero_eq_head, ← C.start_spec,
        C.startFinish]
        rw [← C.steps_getLast_ssnd_eq_finish h, List.getLast_eq_getElem]
        congr
        rw [Nat.add_sub_assoc C.one_le_length, Nat.add_mod]
        simp only [hmod, Nat.self_sub_mod, zero_add, Walk.step_length_eq_length]
      · have := List.chain'_getElem C.next_step (n % C.length - 1)
          (by rw [Nat.sub_lt_sub_iff_right (by omega)]; exact Nat.mod_lt n (C.one_le_length))
        convert this using 1 <;> congr
        · rw [← Nat.mod_sub_eq_sub_mod]
          all_goals simp only [Walk.step_length_eq_length, Nat.add_mod_right]
          omega
        · rw [Nat.sub_add_cancel]
          rfl
          omega
  stepsNeNil := by
    have := C.stepsNeNil
    simp only [Walk.edges, ne_eq, List.map_eq_nil_iff] at this
    simpa only [Walk.edges, ne_eq, List.map_eq_nil_iff, List.rotate_eq_nil_iff]

@[simp]
lemma rotate_edges (C : G.Closed) (n : ℕ) : (C.rotate n).edges = C.edges.rotate n := by
  simp only [Walk.edges, rotate, List.map_rotate]

/-- Pick a vertex, v, in a ClosedWalk. Get a walk from v to v along the ClosedWalk -/
def cut (C : G.Closed) {v : V} (_ : v ∈ C.vertices) : G.Walk :=
  let i := C.vertices.idxOf v
  (C.rotate i).toWalk

/-- Pick 2 vertices, u & v, in a ClosedWalk. Get edge-disjoint paths u to v and v to u -/
def split (C : G.Closed) {u v : V} (hu : u ∈ C.vertices) (hv : v ∈ C.vertices) : G.Path × G.Path :=
  sorry

end Closed

structure Cycle extends Closed G where
  vNodup' : toWalk.vertices.tail.Nodup
  eNodup' : toWalk.edges.Nodup

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

-- instance instFintype [Fintype E] [DecidableEq E] : Fintype (Cycle G) where
--   elems := sorry
--   complete := sorry

lemma vertices_dropLast_nodup {C : G.Cycle} : C.vertices.dropLast.Nodup := by
  have := C.vNodup'
  rwa [Closed.vertices_tail_eq_vertices_dropLast_rotate, List.nodup_rotate] at this

def ofLoop (e : E) (he : G.isLoop e) : G.Cycle where
  toClosed := Closed.ofLoop e he
  vNodup' := by simp only [Walk.vertices, Closed.ofLoop, Walk.some, List.map_cons, List.map_nil,
    List.tail_cons, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  eNodup' := by simp only [Closed.ofLoop, Walk.some_edges, List.nodup_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_self]

def CycleGraph_Emb [Undirected G] (C : G.Cycle) :
    (CycleGraph C.length).Emb G where
  toHom := C.exist_CycleGraph_Hom
  fᵥinj v w h := by
    ext
    simp only [Closed.exist_CycleGraph_Hom] at h
    have h1 : C.length ≤ C.vertices.length := by simp only [Walk.vertices_length,
      le_add_iff_nonneg_right, zero_le]
    rw [List.getElem_val_eq_self h1 (htake := by simp only [List.length_take, Walk.vertices_length,
        le_add_iff_nonneg_right, zero_le, inf_of_le_left, Fin.is_lt])] at h
    conv at h =>
      rhs
      rw [List.getElem_val_eq_self (by simp only [Walk.vertices_length, le_add_iff_nonneg_right,
        zero_le]) (htake := by simp)]
    have : C.length + 1 = C.vertices.length := by simp only [Walk.vertices_length]
    simp_rw [List.take_eq_dropLast this] at h
    rwa [List.Nodup.getElem_inj_iff C.vertices_dropLast_nodup] at h
  fₑinj e1 e2 h := by
    ext
    simp only [Closed.exist_CycleGraph_Hom] at h
    rwa [List.Nodup.getElem_inj_iff C.eNodup'] at h

-- def CycleGraph_equiv_subgraph [Undirected G] [DecidableEq E] (C : G.Cycle) (n : ℕ+)
--     (hn : n.val = C.length) : (CycleGraph n) ≃ᴳ
--     (G.toSubgraph (Sᵥ := C.vertices.toFinset) (Sₑ := C.edges.toFinset) (fun e he v hv => by
--       simp only [List.coe_toFinset, Set.mem_setOf_eq] at he ⊢
--       exact Walk.mem_vertices_of_mem_inc_edges C.toWalk he hv)).val where
--   fᵥ v := by
--     have hv : v.val < C.vertices.length := by
--       simp only [Walk.vertices_length, ← hn]
--       omega
--     refine ⟨C.vertices[v.val], ?_⟩
--     simp only [List.coe_toFinset, toSubgraph_val_Sᵥ, Set.mem_setOf_eq, List.getElem_mem]
--   fₑ e := by
--     have he : e.val < C.edges.length := by
--       simp only [Walk.edges_length, ← hn, Fin.is_lt]
--     refine ⟨C.edges[e.val], ?_⟩
--     simp only [List.coe_toFinset, toSubgraph_val_Sₑ, Set.mem_setOf_eq, List.getElem_mem]
--   inc e := by
--     simp only [toSubgraph_val_inc, Walk.inc_edges_getElem_eq_steps_fst_ssnd, pmap_undir, CycleGraph,
--       map_undir, Sym2.map_pair_eq, undir.injEq, Sym2.pmap_pair]
--     simp only [Finset.coe_sort_coe, id_eq, Set.mem_setOf_eq, eq_mp_eq_cast, eq_mpr_eq_cast,
--       toSubgraph_val_Sᵥ, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq, Prod.swap_prod_mk]
--     left
--     refine ⟨?_, ?_⟩
--     · exact C.steps_getElem_fst_eq_vertices_getElem e.val _ _
--     · convert C.steps_getElem_snd_snd_eq_vertices_getElem_add_one e.val _ _


def OfPathEndsAdj (P : G.Path) (e : E) (he : G.canGo P.finish e P.start) (h : e ∉ P.edges) :
    G.Cycle where
  toClosed := Closed.ofWalkEndAdj P.toWalk e he
  vNodup' := by
    simp only [Closed.ofWalkEndAdj_vertices, ne_eq, Walk.vertices_ne_nil, not_false_eq_true,
      List.tail_append_of_ne_nil]
    rw [List.IsRotated.nodup_iff]
    exact P.vNodup
    convert List.IsRotated.forall _ 1
    rw [List.rotate_eq_drop_append_take (by simp only [Walk.vertices_length, le_add_iff_nonneg_left,
      zero_le])]
    simp only [List.drop_one, List.append_cancel_left_eq, List.take_one, Walk.vertices]
    rfl
  eNodup' := by
    simp only [Closed.ofWalkEndAdj, Walk.append_edges, Walk.some_edges]
    rw [List.nodup_append]
    simp only [P.edges_nodup, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_self, List.disjoint_singleton, h]

lemma not_simple_of_length_two {C : G.Cycle} (hC : C.length = 2) : ¬ G.Simple := by
  rintro hSimple
  obtain hInj := hSimple.inc_inj
  rw [← Walk.edges_length, List.length_eq_two] at hC
  obtain ⟨e1, e2, H⟩ := hC
  have hlen : C.length = 2 := by
    rw [← Walk.edges_length, H]
    rfl
  specialize @hInj e1 e2 ?_
  · rw [inc_eq_get, inc_eq_get, undir.injEq]
    have h1 := C.step_spec' 0 (by simp only [Nat.pos_of_neZero_simp])
    simp only [H, List.getElem_cons_zero, zero_add, ← get_eq_iff_canGo] at h1
    have h2 := C.step_spec' 1 (by omega)
    simp only [H, List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceAdd, ←
      get_eq_iff_canGo] at h2
    simp only [h1, h2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true]
    right
    convert C.startFinish
    rw [Walk.finish, ← List.getElem_length_sub_one_eq_getLast _ (Nat.lt_add_one (C.vertices.length - 1))]
    simp only [Walk.vertices_length, hlen, Nat.reduceAdd, Nat.add_one_sub_one]
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

/-- Pick a vertex, v, in a cycle. Get a walk from v to v along the cycle -/
def cut (C : G.Cycle) {v : V} (_ : v ∈ C.vertices) : G.Walk :=
  let i := C.vertices.idxOf v
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
  stepsNeNil := by
    simp only [walk_steps, ne_eq, List.map_eq_nil_iff, C.stepsNeNil, not_false_eq_true]

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
