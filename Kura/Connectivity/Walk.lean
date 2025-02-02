import Kura.Graph.Add
import Kura.Dep.List
import Kura.Examples.Defs

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] (G : Graph V E)


private def walkAux (P : V → E → V → Prop) : V → List (E × V) → Prop
  | _, [] => True
  | u, w :: ws => P u w.fst w.snd ∧ walkAux P w.snd ws

@[ext]
structure Walk where
  start : V
  steps : List (V × E × V)
  start_spec : (hn : steps ≠ []) → start = (steps.head hn).fst
  step_spec : ∀ uev ∈ steps, G.canGo uev.1 uev.2.1 uev.2.2
  next_step : steps.Chain' (λ a b => a.2.2 = b.1)

namespace Walk
variable {G : Graph V E} (w : Walk G)

lemma ext_iff_ne_nil (w₁ w₂ : Walk G) (h : w₁.steps ≠ []) : w₁ = w₂ ↔ w₁.steps = w₂.steps := by
  constructor
  · exact congrArg steps
  · intro heq
    ext
    · rw [w₁.start_spec h, w₂.start_spec (heq ▸ h)]
      congr
    · rw [heq]

lemma ext_iff_ne_nil' (w₁ w₂ : Walk G) (h : w₂.steps ≠ []) : w₁ = w₂ ↔ w₁.steps = w₂.steps := by
  convert ext_iff_ne_nil w₂ w₁ h using 1 <;> rw [eq_comm]

instance instDecidableEqWalk [DecidableEq E] : DecidableEq G.Walk :=
  fun _ _ => decidable_of_decidable_of_iff Walk.ext_iff.symm

def finish : V := match h : w.steps with
  | [] => w.start
  | a :: as => (w.steps.getLast (h ▸ List.cons_ne_nil a as)).snd.snd

lemma finish_eq_start (h : w.steps = []) : w.finish = w.start := by
  unfold finish
  split
  next h => exact rfl
  next a as has => exfalso; simp only [has, reduceCtorEq] at h

lemma steps_getLast_ssnd_eq_finish (hn : w.steps ≠ []) : w.finish = (w.steps.getLast hn).snd.snd := by
  unfold finish
  split
  next h => exact (hn h).elim
  next a as has => rfl

lemma steps_head_fst_eq_start (hn : w.steps ≠ []) : w.start = (w.steps.head hn).fst :=
  w.start_spec hn

def length : ℕ := w.steps.length

lemma length_eq_zero_iff : w.length = 0 ↔ w.steps = [] := by
  simp only [length, List.length_eq_zero]

lemma length_ne_zero_iff : w.length ≠ 0 ↔ w.steps ≠ [] := by
  simp only [length, ne_eq, List.length_eq_zero]

def isSubpath : Walk G → Walk G → Prop := λ w₁ w₂ => w₁.steps.IsInfix w₂.steps

def vertices : List V :=
  w.start :: w.steps.map (·.snd.snd)

@[simp]
lemma vertices_ne_nil : w.vertices ≠ [] := by
  simp only [vertices, ne_eq, List.cons_ne_nil, not_false_eq_true]

-- lemma start_mem_vertices : w.start ∈ w.vertices := by
--   simp only [vertices, start, List.mem_cons, List.mem_map, Prod.exists, exists_eq_right, true_or]

-- lemma finish_mem_vertices : w.finish ∈ w.vertices := by
--   simp only [vertices, finish, List.mem_cons, List.mem_map, exists_eq_right]
--   split
--   next h => exact Or.inl rfl
--   next a as h =>
--     right
--     use w.steps.getLast (h ▸ List.cons_ne_nil a as)
--     simp only [List.getLast_mem, and_self]

lemma steps_fst_vertices : w.steps.map (·.fst) = w.vertices.dropLast := by
  match h : w.steps with
  | [] => simp only [h, List.map_nil, vertices, List.dropLast_single]
  | [a] =>
    have hstart := w.start_spec (h ▸ List.cons_ne_nil a _)
    simp_all only [List.head_cons, List.map_cons, List.map_nil, vertices, List.dropLast_cons₂,
      List.dropLast_single]
  | a :: a' :: as =>
    have hstart := w.start_spec (h ▸ List.cons_ne_nil a (a' :: as))
    have hchain := w.next_step
    simp_all [List.Chain', List.chain_iff_forall₂, vertices]
    rw [eq_comm, ← List.forall₂_eq_eq_eq]
    obtain ⟨ha', hchain⟩ := hchain
    rw [← List.forall₂_map_right_iff, ← List.forall₂_map_left_iff] at hchain
    convert hchain
    simp only [List.map_dropLast, List.map_cons]

lemma steps_ssnd_vertices : w.steps.map (·.snd.snd) = w.vertices.tail := by
  simp only [vertices, List.tail_cons]

@[simp]
lemma vertices_head_eq_start : w.vertices.head w.vertices_ne_nil = w.start := rfl

@[simp]
lemma vertices_getLast_eq_finish : w.vertices.getLast (w.vertices_ne_nil) = w.finish := by
  unfold finish vertices
  split
  next h =>
    have : [w.start].getLast (List.cons_ne_nil w.start []) = w.start := by rfl
    convert this
    simp only [h, List.map_nil]
  next a as h =>
    rw [List.getLast_cons (by simp only [h, List.map_cons, ne_eq, reduceCtorEq, not_false_eq_true])]
    simp only [List.getLast_map]

lemma vertices_chain'_adj : w.vertices.Chain' G.adj :=
  match h : w.vertices with
  | [] => (w.vertices_ne_nil h).elim
  | [a] => List.chain'_singleton a
  | a :: a' :: as => by
    simp [List.Chain', List.chain_iff_forall₂, reduceCtorEq, false_or, -List.forall₂_cons]
    rw [← List.dropLast_cons₂, ← h, ← steps_fst_vertices, ← @List.tail_cons _ (a := a) (a' :: as),
      ← h, ← steps_ssnd_vertices, List.forall₂_map_right_iff, List.forall₂_map_left_iff,
      List.forall₂_same]
    intro x hx
    use x.2.1
    exact w.step_spec x hx

@[simp]
lemma vertices_length : w.vertices.length = w.length + 1 := by
  simp only [vertices, length, List.length_cons, List.length_map]

def edges : List E := w.steps.map (·.snd.fst)

lemma length_ne_zero_iff_edges_ne_nil : w.length ≠ 0 ↔ w.edges ≠ [] := by
  simp only [ne_eq, length_ne_zero_iff, edges, List.map_eq_nil_iff]

@[simp]
lemma edges_length : w.edges.length = w.length := by
  simp only [edges, length, List.length_map]

-- same path iff same start and same edges

def nil (u : V) : Walk G where
  start := u
  steps := []
  start_spec := fun hn => (hn rfl).elim
  step_spec := fun uev hin => (List.not_mem_nil uev hin).elim
  next_step := List.chain'_nil

@[simp]
lemma nil_start (u : V) : (nil (G := G) u).start = u := rfl

@[simp]
lemma nil_steps (u : V) : (nil (G := G) u).steps = [] := rfl

@[simp]
lemma nil_length (u : V) : (nil (G := G) u).length = 0 := rfl

@[simp]
lemma nil_finish (u : V) : (nil (G := G) u).finish = u := by simp only [finish, nil]

lemma nil_of_length_zero (w : Walk G) (h : w.length = 0) : w = nil w.start := by
  ext n s
  rfl
  simp only [length, List.length_eq_zero] at h
  simp only [h, List.getElem?_nil, Option.mem_def, reduceCtorEq, nil_steps]

@[simp]
lemma length_zero_iff_eq_nil (w : Walk G) : w.length = 0 ↔ w = nil w.start  := by
  constructor
  · exact nil_of_length_zero w
  · intro h
    rw [h]
    rfl

lemma length_pos_of_start_ne_finish (w : Walk G) (h : w.start ≠ w.finish) : w.length ≠ 0 := by
  rintro hlen
  have hnil := w.length_zero_iff_eq_nil.mp hlen
  rw [hnil] at h
  simp only [nil_start, nil_finish, ne_eq, not_true_eq_false] at h

@[simp]
lemma nil_vertices (u : V) : (nil (G := G) u).vertices = [u] := by
  simp only [vertices, nil_start, nil_steps, List.map_nil]

@[simp]
lemma mem_nil_vertices (u v : V) : v ∈ (nil (G := G) u).vertices ↔ v = u := List.mem_singleton

@[simp]
lemma nil_edges (u : V) : (nil (G := G) u).edges = [] := by
  simp only [edges, nil_steps, List.map_nil]

@[simp]
lemma not_mem_nil_edges (e : E) : e ∉ (nil (G := G) u).edges := List.not_mem_nil e

lemma eq_nil_iff_edges_nil (w : Walk G) : w = nil w.start ↔ w.edges = [] := by
  constructor
  · intro h
    rw [h]
    exact nil_edges _
  · intro h
    simp [edges] at h
    ext1
    · rfl
    · rw [h]
      rfl

lemma eq_nil [IsEmpty E] (w : Walk G) : w = nil w.start := by
  rw [eq_nil_iff_edges_nil]
  exact List.eq_nil_of_IsEmpty w.edges

def some (u : V) (e : E) (v : V) (h : G.canGo u e v) : Walk G where
  start := u
  steps := [(u, e, v)]
  start_spec := fun hn => by rw [List.head_cons]
  step_spec := fun uev hin => by
    rw [List.mem_singleton] at hin
    rw [hin]
    exact h
  next_step := List.chain'_singleton _

@[simp]
lemma some_start (u : V) (e : E) (v : V) (h : G.canGo u e v) : (some u e v h).start = u := rfl

@[simp]
lemma some_finish (u : V) (e : E) (v : V) (h : G.canGo u e v) : (some u e v h).finish = v := rfl

@[simp]
lemma some_vertices (u : V) (e : E) (v : V) (h : G.canGo u e v) : (some u e v h).vertices = [u, v] := by
  simp only [vertices, some, List.map_cons, List.map_nil]

@[simp]
lemma some_edges (u : V) (e : E) (v : V) (h : G.canGo u e v) : (some u e v h).edges = [e] := by
  simp only [edges, some, List.map_cons, List.map_nil]

def append (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) : Walk G where
  start := w₁.start
  steps := w₁.steps ++ w₂.steps
  start_spec := by
    intro hn
    simp only [List.head_append hn, List.isEmpty_eq_true]
    split_ifs with h
    · rw [List.isEmpty_iff] at h
      simp only [h] at hn
      rw [w₁.finish_eq_start h] at hconn
      exact hconn ▸ w₂.start_spec hn
    · simp only [List.isEmpty_eq_true] at h
      exact w₁.start_spec h
  step_spec := by
    intro uev hin
    rw [List.mem_append] at hin
    rcases hin with hin₁ | hin₂
    · exact w₁.step_spec uev hin₁
    · exact w₂.step_spec uev hin₂
  next_step := by
    refine List.Chain'.append w₁.next_step w₂.next_step ?_
    intro a ha b hb
    convert hconn
    · obtain ⟨hn, rfl⟩ := List.mem_getLast?_eq_getLast ha
      exact Eq.symm (w₁.steps_getLast_ssnd_eq_finish hn)
    · have hn := List.ne_nil_of_mem (List.mem_of_mem_head? hb)
      rw [Option.mem_iff, ← List.head_eq_iff_head?_eq_some hn] at hb
      exact hb ▸ (w₂.start_spec hn).symm

lemma append_start (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) :
    (w₁.append w₂ hconn).start = w₁.start := rfl

lemma append_finish (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) :
    (w₁.append w₂ hconn).finish = w₂.finish := by
  simp [append, finish]
  split
  rename_i happ
  simp at happ
  · split
    · rw [← hconn]
      exact (w₁.finish_eq_start happ.1).symm
    · exfalso
      simp_all
  · rename_i a as happ
    split
    · rename_i h2
      rw [List.getLast_append]
      simp only [h2, List.isEmpty_nil, ↓reduceDIte]
      have h1 : w₁.steps ≠ [] := by
        simp [h2] at happ
        simp [happ]
      rw [← hconn, w₁.steps_getLast_ssnd_eq_finish h1]
    · rename_i b bs h2
      rw [List.getLast_append]
      simp only [h2, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte]

@[simp]
lemma append_length (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) :
    (w₁.append w₂ hconn).length = w₁.length + w₂.length := by
  simp only [length, append, List.length_append]

@[simp]
lemma append_vertices (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) :
    (w₁.append w₂ hconn).vertices = w₁.vertices ++ w₂.vertices.tail := by
  simp only [vertices, append, List.map_append, List.tail_cons, List.cons_append]

@[simp]
lemma append_edges (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) :
    (w₁.append w₂ hconn).edges = w₁.edges ++ w₂.edges := by
  simp only [edges, append, List.map_append]

@[simp]
lemma some_append_length (u : V) (e : E) (v : V) (h : G.canGo u e v) (w : Walk G)
  (hconn : v = w.start) :
    ((some u e v h).append w hconn).length = w.length + 1 := by
  simp only [length, append, some, List.singleton_append, List.length_cons]

@[simp]
lemma append_some_length (w : Walk G) (u : V) (e : E) (v : V) (h : G.canGo u e v)
  (hconn : w.finish = u) :
    (w.append (some u e v h) hconn).length = w.length + 1 := by
  simp only [length, append, some, List.length_append, List.length_singleton]

lemma of_chain'_adj {u : V} {l : List V} (h : l.Chain G.adj u) :
    ∃ w : Walk G, w.vertices = (u ::l) := by
  induction l generalizing u with
  | nil => exact ⟨nil u, nil_vertices u⟩
  | cons v vs ih =>
    specialize ih (List.chain_of_chain_cons h)
    obtain ⟨w, hw⟩ := ih
    rw [List.chain_cons] at h
    obtain ⟨⟨e, he⟩, hvs⟩ := h
    let w' := some u e v he
    use w'.append w (by simp only [some_finish, ← vertices_head_eq_start, hw, List.head_cons, w'])
    simp only [append_vertices, some_vertices, hw, List.tail_cons, List.cons_append,
      List.singleton_append, w', List.nil_append]

def take (w : Walk G) (n : ℕ) : Walk G where
  start := w.start
  steps := w.steps.take n
  start_spec := by
    intro hn
    rw [List.head_take hn]
    exact w.start_spec (List.ne_nil_of_take_ne_nil hn)
  step_spec := by
    intro uev hin
    refine w.step_spec uev (List.mem_of_mem_take hin)
  next_step := List.Chain'.take w.next_step _

@[simp]
lemma take_length_eq_min (w : Walk G) (n : ℕ) : (w.take n).length = min n w.length := by
  simp only [length, take, List.length_take]

@[simp]
lemma take_eq_self (w : Walk G) (n : ℕ) (hn : w.length ≤ n): w.take n = w := by
  rw [Walk.ext_iff]
  refine ⟨rfl, ?_⟩
  simp only [take, List.take_of_length_le hn]

def stopAt (w : Walk G) (v : V) : Walk G where
  start := w.start
  steps := w.steps.take (w.steps.map (fun x ↦ x.2.2) |>.indexOf v)
  start_spec := by
    intro hn
    rw [List.head_take hn]
    exact w.start_spec (List.ne_nil_of_take_ne_nil hn)
  step_spec := by
    intro uev hin
    refine w.step_spec uev (List.mem_of_mem_take hin)
  next_step := List.Chain'.take w.next_step _

lemma stopAt_vertices_IsPrefix (w : Walk G) (v : V) :
    (w.stopAt v).vertices.IsPrefix w.vertices := by
  simp only [vertices, stopAt, List.map_take, List.cons_prefix_cons, true_and]
  exact List.take_prefix (List.indexOf v (List.map (fun x ↦ x.2.2) w.steps))
      (List.map (fun x ↦ x.2.2) w.steps)

@[simp]
lemma stopAt_start (v : V) :
  (w.stopAt v).start = w.start := rfl

@[simp]
lemma stopAt_finish (v : V) (hv : v ∈ w.vertices) : (w.stopAt v).finish = v := by
  sorry

lemma stopAt_steps_eq_nil_iff (v : V) (hw : w.steps ≠ []) :
    (w.stopAt v).steps = [] ↔ v = w.start := by
  sorry

def startFrom (v : V) : Walk G where
  start := v
  steps := w.steps.drop (w.vertices.indexOf v)
  start_spec := by
    rintro hn
    simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hn
    simp only [List.head_drop]
    sorry
  step_spec := by
    intro uev hin
    refine w.step_spec uev (List.mem_of_mem_drop hin)
  next_step := List.Chain'.drop w.next_step _

lemma startFrom_vertices_IsSuffix (w : Walk G) (v : V) :
  (w.startFrom v).vertices.IsSuffix w.vertices := by
  sorry

lemma startFrom_start (w : Walk G) (v : V) :
  (w.startFrom v).start = v := by
  sorry

def meet (w₁ w₂ : Walk G) (h : w₁.finish = w₂.start) :=
  (w₁.vertices.find? (· ∈ w₂.vertices)).get (by
    simp only [List.find?_isSome, decide_eq_true_eq]
    use w₁.finish
    use w₁.vertices_getLast_eq_finish ▸ List.getLast_mem w₁.vertices_ne_nil
    use h ▸ w₂.vertices_head_eq_start ▸ List.head_mem w₂.vertices_ne_nil)

lemma meet_mem_left (w₁ w₂ : Walk G) (h : w₁.finish = w₂.start) : w₁.meet w₂ h ∈ w₁.vertices := by
  simp only [meet, List.get_find?_mem]

lemma meet_mem_right (w₁ w₂ : Walk G) (h : w₁.finish = w₂.start) : w₁.meet w₂ h ∈ w₂.vertices := by
  simp only [meet]
  sorry

lemma left_indexOf_meet_eq_zero_eq_start (w₁ w₂ : Walk G) (h : w₁.finish = w₂.start) :
  w₁.vertices.indexOf (w₁.meet w₂ h) = 0 ↔ (w₁.meet w₂ h) = w₁.start := by
  constructor
  · intro hz
    rw [← List.indexOf_inj (meet_mem_left w₁ w₂ h), hz]
    unfold vertices
    rw [List.indexOf_cons_self]
    apply List.mem_cons_self
  · intro hms
    refine List.indexOf_cons_eq _ hms.symm

def reverse [Undirected G] (w : Walk G) : Walk G where
  start := w.finish
  steps := w.steps.reverse.map (λ ⟨u, e, v⟩ => (v, e, u))
  start_spec := by
    intro hn
    simp only [List.map_reverse, ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil_iff] at hn
    unfold finish
    split
    · exfalso
      exact hn (by assumption)
    · simp only [List.map_reverse, List.head_reverse, List.getLast_map]
  step_spec := by
    intro uev hin
    rw [List.mem_map] at hin
    rcases hin with ⟨⟨u, e, v⟩, hin, rfl⟩
    rw [List.mem_reverse] at hin
    refine (G.canGo_symm e _ _) ▸ (w.step_spec _ hin)
  next_step := by
    rw [List.chain'_map, List.chain'_reverse]
    unfold _root_.flip
    convert w.next_step using 3
    rw [Eq.comm]

@[simp]
lemma reverse_start [Undirected G] (w : Walk G) : (w.reverse).start = w.finish := rfl

@[simp]
lemma reverse_finish [Undirected G] (w : Walk G) : (w.reverse).finish = w.start := by
  simp only [finish, reverse, List.map_reverse, List.getLast_reverse, List.head_map]
  split
  · rename_i h
    simp at h
    split
    · rfl
    · exfalso
      rename_i hcons
      exact (hcons ▸ List.cons_ne_nil _ _) h
  · apply (w.start_spec _).symm

@[simp]
lemma reverse_vertices [Undirected G] (w : Walk G) : (w.reverse).vertices = w.vertices.reverse := by
  sorry

-- def extensions (w : Walk G) [Fintype E] [DecidableEq E] : Finset (Walk G) :=
--   let u := w.finish
--   let es : Finset _ := ((G.outEdges u).filter fun e => (G.gofrom? u e).isSome).attach
--   es.image (fun e => w.append (some u e.val ((G.gofrom? u e.val).get (by
--     obtain ⟨e, he⟩ := e
--     simp only [gofrom?, Finset.mem_filter] at he
--     exact he.2)) sorry) (by rw [some_start]))

-- lemma mem_extensions_length (w w' : Walk G) [Fintype E] [DecidableEq E] :
--     w' ∈ w.extensions → w'.length = w.length + 1 := by
--   intro h
--   simp only [extensions, Finset.mem_image] at h
--   rcases h with ⟨e, _he, h⟩
--   rw [← h, w.append_some_length]

-- def Nextensions (W : Finset G.Walk) [Fintype E] [DecidableEq E] : Finset G.Walk :=
--   W.biUnion (·.extensions)

-- lemma mem_extensions_of_length [Fintype E] [DecidableEq E] (n : ℕ) (w : Walk G)
--   (hwlen : w.length = n) :
--   w ∈ ((Finset.biUnion · (·.extensions))^[n] {Walk.nil w.start}) := by
--   induction n generalizing w with
--   | zero =>
--     simpa only [Function.iterate_zero, id_eq, Finset.mem_singleton, nil_iff_length_zero]
--   | succ n ih =>
--     rw [Function.iterate_succ']
--     simp only [Function.comp_apply, Finset.mem_biUnion]
--     use w.take n
--     specialize ih (w.take n) (by simp only [take_length_eq_min, hwlen, le_add_iff_nonneg_right,
--       zero_le, min_eq_left])
--     use ih
--     sorry

end Walk

namespace Emb

def walk [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G) (h : G ⊆ᴳ H) : Walk H where
  start := h.fᵥ w.start
  steps := w.steps.map (fun ⟨u, e, v⟩ => (h.fᵥ u, h.fₑ e, h.fᵥ v))
  start_spec hn := by
    simp only [List.head_map, EmbeddingLike.apply_eq_iff_eq]
    congr 1
    apply w.start_spec
  step_spec := by
    simp only [List.mem_map, Prod.exists, canGo, forall_exists_index, and_imp, Prod.forall,
      Prod.mk.injEq]
    rintro w₁ f w₂ v₁ e v₂ hve rfl rfl rfl
    exact h.canGo (w.step_spec (v₁, e, v₂) hve)
  next_step := by
    refine List.chain'_map_of_chain' _ ?_ w.next_step
    rintro ⟨u, e, v⟩ ⟨u', e', v'⟩ h
    simp only
    congr 1

@[simp]
lemma walk_start [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G)
    (h : G ⊆ᴳ H) : (h.walk w).start = h.fᵥ w.start := rfl

@[simp]
lemma walk_steps [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G)
    (h : G ⊆ᴳ H) : (h.walk w).steps = w.steps.map (fun ⟨u, e, v⟩ => (h.fᵥ u, h.fₑ e, h.fᵥ v)) := rfl

@[simp]
lemma walk_vertices [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G)
    (h : G.Emb H) : (h.walk w).vertices = w.vertices.map h.fᵥ := by
  simp only [Walk.vertices, walk, List.map_map, List.map_cons, List.cons.injEq, List.map_inj_left,
    Function.comp_apply, implies_true, and_self]

@[simp]
lemma walk_finish [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G)
    (h : G.Emb H) : (h.walk w).finish = h.fᵥ w.finish := by
  rw [← Walk.vertices_getLast_eq_finish, ← Walk.vertices_getLast_eq_finish]
  simp only [walk_vertices, List.getLast_map, Walk.vertices_getLast_eq_finish]

@[simp]
lemma walk_edges [DecidableEq W] {G : Graph V E} {H : Graph W F} (w : Walk G)
    (h : G.Emb H) : (h.walk w).edges = w.edges.map h.fₑ := by
  simp only [Walk.edges, walk_steps, List.map_map, List.map_inj_left, Function.comp_apply,
    implies_true]

end Emb


@[ext]
structure Path extends Walk G where
  vNodup : toWalk.vertices.Nodup

namespace Path
variable {G : Graph V E}

lemma start_not_mem_vertices_tail (P : Path G): P.start ∉ P.vertices.tail :=
  List.Nodup.not_mem P.vNodup

def stopAt (p : Path G) (v : V) : Path G where
  toWalk := p.toWalk.stopAt v
  vNodup := (p.toWalk.stopAt_vertices_IsPrefix v).sublist.nodup p.vNodup

def startFrom (p : Path G) (v : V) : Path G where
  toWalk := p.toWalk.startFrom v
  vNodup := (p.toWalk.startFrom_vertices_IsSuffix v).sublist.nodup p.vNodup

def nil (u : V) : Path G where
  toWalk := Walk.nil u
  vNodup := List.nodup_singleton _

@[simp]
lemma nil_start (u : V) : (nil (G := G) u).start = u := rfl

@[simp]
lemma nil_steps (u : V) : (nil (G := G) u).steps = [] := rfl

@[simp]
lemma nil_length (u : V) : (nil (G := G) u).length = 0 := rfl

@[simp]
lemma nil_finish (u : V) : (nil (G := G) u).finish = u := Walk.nil_finish u

lemma nil_of_length_zero (p : Path G) (h : p.length = 0) : p = nil p.start := by
  ext n s
  rfl
  simp only [Walk.length, List.length_eq_zero] at h
  simp only [h, List.getElem?_nil, Option.mem_def, reduceCtorEq, nil_steps]

@[simp]
lemma length_zero_iff_eq_nil (p : Path G) : p.length = 0 ↔ p = nil p.start  := by
  constructor
  · exact nil_of_length_zero p
  · intro h
    rw [h]
    rfl

@[simp]
lemma nil_vertices (u : V) : (nil (G := G) u).vertices = [u] := by
  simp only [Walk.vertices, nil_start, nil_steps, List.map_nil]

@[simp]
lemma mem_nil_vertices (u v : V) : v ∈ (nil (G := G) u).vertices ↔ v = u := List.mem_singleton

@[simp]
lemma nil_edges (u : V) : (nil (G := G) u).edges = [] := by
  simp only [Walk.edges, nil_steps, List.map_nil]

@[simp]
lemma not_mem_nil_edges (e : E) : e ∉ (nil (G := G) u).edges := List.not_mem_nil e

def some (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) : Path G where
  toWalk := Walk.some u e v hgo
  vNodup := by simp only [Walk.vertices, Walk.some, List.map_cons, List.map_nil, List.nodup_cons,
    List.mem_singleton, hnloop, not_false_eq_true, List.not_mem_nil, List.nodup_nil, and_self]

@[simp]
lemma some_start (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) :
    (some u e v hgo hnloop).start = u := rfl

@[simp]
lemma some_finish (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) :
    (some u e v hgo hnloop).finish = v := rfl

@[simp]
lemma mem_some_vertices (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) (w : V) :
    w ∈ (some u e v hgo hnloop).vertices ↔ w = u ∨ w = v := by
  simp only [Walk.vertices, some, Walk.some, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false]

@[simp]
lemma mem_some_edges (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) (w : E) :
    w ∈ (some u e v hgo hnloop).edges ↔ w = e := by
  simp only [Walk.edges, some, Walk.some, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]

/-- Append two paths. To keep the result vertex unique, take the second path in the first shared vertex. -/
-- def append (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) : Path G where
--   start := p₁.start
--   steps := (p₁.stopAt (p₁.meet p₂.toWalk hfs)).steps ++ (p₂.startFrom (p₁.meet p₂.toWalk hfs)).steps
--   start_spec := by
--     intro hn
--     rw [List.head_append hn]
--     split_ifs with h
--     · simp only [stopAt, Walk.stopAt, List.isEmpty_eq_true, List.take_eq_nil_iff, ne_eq,
--       Walk.vertices_ne_nil, not_false_eq_true, List.indexOf_eq_zero_iff,
--       Walk.vertices_head_eq_start] at h
--       rcases h with h | h
--       · rw [h]
--         convert (p₂.startFrom_start (p₁.meet p₂.toWalk hfs)).symm
--         refine ((p₂.startFrom (p₁.meet p₂.toWalk hfs)).start_spec _).symm
--       · rw [← Walk.finish_eq_start _ h, hfs]
--         rename_i hstop
--         simp only [List.isEmpty_eq_true] at hstop
--         rw [← Walk.length_eq_zero_iff, length_zero_iff_eq_nil] at h
--         sorry
--     · convert (p₁.stopAt_start (p₁.meet p₂.toWalk hfs)).symm
--       refine ((p₁.stopAt (p₁.meet p₂.toWalk hfs)).start_spec _).symm
--   step_spec := by
--     intro uev hin
--     rw [List.mem_append] at hin
--     rcases hin with hin₁| hin₂
--     · refine p₁.step_spec uev (List.mem_of_mem_take hin₁)
--     · refine p₂.step_spec uev (List.mem_of_mem_drop hin₂)
--   next_step := by
--     refine List.Chain'.append (p₁.next_step.take _) (p₂.next_step.drop _) ?_
--     intro a ha b hb
--     simp at ha hb

    -- simp [List.getLast?_take] at ha
    -- split_ifs at ha with hi
    -- simp at ha

    -- simp [List.head?_drop] at hb
    -- have : ∃ n : ℕ, List.indexOf (p₁.meet p₂ h) p₂.vertices.reverse = 1 + n := by
    --   sorry
    -- obtain ⟨n, hn⟩ := this
    -- rw [hn, Nat.sub_add_eq, ← List.getElem?_reverse] at hb


    -- rw [List.getLast?_eq_some_iff] at ha
    -- obtain ⟨L1, hL1⟩ := ha
    -- apply_fun (·.map (·.snd.snd)) at hL1
    -- simp [Walk.steps_ssnd_vertices] at hL1
    -- apply_fun (·.getLast?) at hL1
    -- simp [List.getLast?_take] at hL1
    -- split_ifs at hL1 with h
    -- simp only [Option.or_eq_some, List.getElem?_eq_none_iff, List.length_tail, tsub_le_iff_right] at hL1

  --   sorry
  -- vNodup := by
  --   sorry

-- @[simp]
-- lemma append_start (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) :
--     (p₁.append p₂ hfs).start = p₁.start := rfl

-- @[simp]
-- lemma append_finish (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) :
--     (p₁.append p₂ hfs).finish = p₂.finish := by
--   sorry

-- @[simp]
-- lemma mem_append_vertices (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) (v : V) :
--     v ∈ (p₁.append p₂ hfs).vertices ↔ v ∈ p₁.vertices ∨ v ∈ p₂.vertices := by
--   sorry

-- @[simp]
-- lemma mem_append_edges (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) (e : E) :
--     e ∈ (p₁.append p₂ hfs).edges ↔ e ∈ p₁.edges ∨ e ∈ p₂.edges := by
--   sorry


def reverse [Undirected G] (p : Path G) : Path G where
  toWalk := p.toWalk.reverse
  vNodup := by
    rw [Walk.reverse_vertices, List.nodup_reverse]
    exact p.vNodup

@[simp]
lemma reverse_start [Undirected G] (p : Path G) : (p.reverse).start = p.finish := rfl

@[simp]
lemma reverse_finish [Undirected G] (p : Path G) : (p.reverse).finish = p.start := p.toWalk.reverse_finish

@[simp]
lemma mem_reverse_vertices [Undirected G] (p : Path G) (v : V) :
    v ∈ p.reverse.vertices ↔ v ∈ p.vertices := by
  sorry

@[simp]
lemma mem_reverse_edges [Undirected G] (p : Path G) (e : E) :
    e ∈ p.reverse.edges ↔ e ∈ p.edges := by
  sorry

end Path

namespace Emb
variable [DecidableEq W] {G : Graph V E} {H : Graph W F} (h : G.Emb H)

def Path (p : Path G)  : Path H where
  toWalk := h.walk p.toWalk
  vNodup := by
    simp only [walk_vertices]
    apply p.vNodup.map h.fᵥinj

variable {p : G.Path}

@[simp]
lemma Path_start : (h.Path p).start = h.fᵥ p.start := rfl

@[simp]
lemma Path_steps : (h.Path p).steps = p.steps.map (fun ⟨u, e, v⟩ => (h.fᵥ u, h.fₑ e, h.fᵥ v)) := rfl

@[simp]
lemma Path_vertices : (h.Path p).vertices = p.vertices.map h.fᵥ := by
  unfold Walk.vertices
  simp only [Path_start, Path_steps, List.map_map, List.map_cons, List.cons.injEq,
    List.map_inj_left, Function.comp_apply, implies_true, and_self]

@[simp]
lemma Path_finish : (h.Path p).finish = h.fᵥ p.finish := by
  rw [← Walk.vertices_getLast_eq_finish, ← Walk.vertices_getLast_eq_finish,
    ← p.vertices.getLast_map h.fᵥ]
  convert rfl
  exact (Path_vertices h).symm
  simp only [ne_eq, List.map_eq_nil_iff, Walk.vertices_ne_nil, not_false_eq_true]

@[simp]
lemma Path_edges : (h.Path p).edges = p.edges.map h.fₑ := by
  simp only [Walk.edges, Path_steps, List.map_map, List.map_inj_left, Function.comp_apply,
    implies_true]

end Emb


structure Trail extends Walk G where
  eNodup : toWalk.edges.Nodup

end Graph
