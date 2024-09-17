import Kura.Finite

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E)

private def walkAux (P : V → E → V → Prop) : V → List (E × V) → Prop
  | _, [] => True
  | u, w :: ws => P u w.fst w.snd ∧ walkAux P w.snd ws

structure Walk where
  start : V
  steps : List (V × E × V)
  start_spec : (hn : steps ≠ []) → start = (steps.head hn).fst
  step_spec : ∀ uev ∈ steps, G.canGo uev.1 uev.2.1 uev.2.2
  next_step : steps.Chain' (λ a b => a.2.2 = b.1)

namespace Walk
variable {G : Graph V E} (w : Walk G)

def finish : V := match h : w.steps with
  | [] => w.start
  | a :: as => (w.steps.getLast (h ▸ List.cons_ne_nil a as)).snd.snd

lemma finish_eq_start (h : w.steps = []) : w.finish = w.start := by
  unfold finish
  split
  next h => exact rfl
  next a as has => exfalso; simp [has] at h

lemma finish_eq_getLast_ssnd (hn : w.steps ≠ []) : w.finish = (w.steps.getLast hn).snd.snd := by
  unfold finish
  split
  next h => exact (hn h).elim
  next a as has => rfl

def length : ℕ := w.steps.length

def isSubpath : Walk G → Walk G → Prop := λ w₁ w₂ => w₁.steps.IsInfix w₂.steps

def vertices : List V :=
  w.start :: w.steps.map (·.snd.snd)

lemma start_mem_vertices : w.start ∈ w.vertices := by
  simp only [vertices, start, List.mem_cons, List.mem_map, Prod.exists, exists_eq_right, true_or]

lemma finish_mem_vertices : w.finish ∈ w.vertices := by
  simp only [vertices, finish, List.mem_cons, List.mem_map, exists_eq_right]
  split
  next h => exact Or.inl rfl
  next a as h =>
    right
    use w.steps.getLast (h ▸ List.cons_ne_nil a as)
    simp only [List.getLast_mem, and_self]

lemma steps_fst_vertices : w.steps.map (·.fst) = w.vertices.dropLast := by
  sorry

lemma steps_ssnd_vertices : w.steps.map (·.snd.snd) = w.vertices.drop 1 := by
  simp only [vertices, List.drop_succ_cons, List.drop_zero]

def edges : List E := w.steps.map (·.snd.fst)

def nil (u : V) : Walk G where
  start := u
  steps := []
  start_spec := fun hn => (hn rfl).elim
  step_spec := fun uev hin => (List.not_mem_nil uev hin).elim
  next_step := List.chain'_nil

@[simp]
lemma nil_finish (u : V) : (nil (G := G) u).finish = u := by simp only [finish, nil]

def some (u : V) (e : E) (v : V) (h : G.canGo u e v) : Walk G where
  start := u
  steps := [(u, e, v)]
  start_spec := fun hn => by rw [List.head_cons]
  step_spec := fun uev hin => by
    rw [List.mem_singleton] at hin
    rw [hin]
    exact h
  next_step := List.chain'_singleton _

def append (w₁ w₂ : Walk G) (hconn : w₁.finish = w₂.start) : Walk G where
  start := w₁.start
  steps := w₁.steps ++ w₂.steps
  start_spec := by
    intro hn
    simp only [List.head_append hn, List.isEmpty_eq_true]
    split_ifs with h
    · rw [List.isEmpty_iff] at h
      simp [h] at hn
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
      exact Eq.symm (w₁.finish_eq_getLast_ssnd hn)
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
      rw [← hconn, w₁.finish_eq_getLast_ssnd h1]
    · rename_i b bs h2
      rw [List.getLast_append]
      simp only [h2, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte]

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

def stopAt (w : Walk G) (v : V) : Walk G where
  start := w.start
  steps := w.steps.take (w.vertices.indexOf v)
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
  sorry

@[simp]
lemma stopAt_start (w : Walk G) (v : V) :
  (w.stopAt v).start = w.start := rfl

@[simp]
lemma stopAt_finish (w : Walk G) (v : V) :
  (w.stopAt v).finish = v := by
  sorry

def startFrom (w : Walk G) (v : V) : Walk G where
  start := v
  steps := w.steps.drop (w.vertices.indexOf v)
  start_spec := by
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
    use w₁.finish_mem_vertices
    use h ▸ w₂.start_mem_vertices)

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
    simp only [List.map_reverse, ne_eq, List.reverse_eq_nil_iff, List.map_eq_nil] at hn
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

end Walk

structure Path extends Walk G where
  vNodup : toWalk.vertices.Nodup

namespace Path
variable {G : Graph V E}

def stopAt (p : Path G) (v : V) : Path G where
  toWalk := p.toWalk.stopAt v
  vNodup := (p.toWalk.stopAt_vertices_IsPrefix v).sublist.nodup p.vNodup

def startFrom (p : Path G) (v : V) : Path G where
  toWalk := p.toWalk.startFrom v
  vNodup := (p.toWalk.startFrom_vertices_IsSuffix v).sublist.nodup p.vNodup

def nil (u : V) : Path G where
  toWalk := Walk.nil u
  vNodup := List.nodup_singleton _

lemma nil_finish (u : V) : (nil (G := G) u).finish = u := Walk.nil_finish u

lemma not_mem_edges_nil (e : E) : e ∉ (nil (G := G) u).edges := List.not_mem_nil e

def some (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) : Path G where
  toWalk := Walk.some u e v hgo
  vNodup := by simp only [Walk.vertices, Walk.some, List.map_cons, List.map_nil, List.nodup_cons,
    List.mem_singleton, hnloop, not_false_eq_true, List.not_mem_nil, List.nodup_nil, and_self]

lemma some_start (u : V) (e : E) (v : V) (hgo : G.canGo u e v) (hnloop : u ≠ v) :
    (some u e v hgo hnloop).start = u := rfl

/-- Append two paths. To keep the result vertex unique, take the second path in the first shared vertex. -/
def append (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) : Path G where
  start := p₁.start
  steps := (p₁.stopAt (p₁.meet p₂.toWalk hfs)).steps ++ (p₂.startFrom (p₁.meet p₂.toWalk hfs)).steps
  start_spec := by
    intro hn
    rw [List.head_append hn]
    split_ifs with h
    · simp [List.isEmpty_eq_true, stopAt, Walk.stopAt] at h
      rcases h with h | h
      · rw [Walk.left_indexOf_meet_eq_zero_eq_start] at h
        rw [← h]
        convert (p₂.startFrom_start (p₁.meet p₂.toWalk hfs)).symm
        refine ((p₂.startFrom (p₁.meet p₂.toWalk hfs)).start_spec _).symm
      · rw [← Walk.finish_eq_start _ h, hfs]
        sorry
    · convert (p₁.stopAt_start (p₁.meet p₂.toWalk hfs)).symm
      refine ((p₁.stopAt (p₁.meet p₂.toWalk hfs)).start_spec _).symm
  step_spec := by
    intro uev hin
    rw [List.mem_append] at hin
    rcases hin with hin₁| hin₂
    · refine p₁.step_spec uev (List.mem_of_mem_take hin₁)
    · refine p₂.step_spec uev (List.mem_of_mem_drop hin₂)
  next_step := by
    refine List.Chain'.append (p₁.next_step.take _) (p₂.next_step.drop _) ?_
    intro a ha b hb
    simp at ha hb

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

    sorry
  vNodup := by
    sorry

lemma append_start (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) :
    (p₁.append p₂ hfs).start = p₁.start := rfl

lemma append_finish (p₁ p₂ : Path G) (hfs : p₁.finish = p₂.start) :
    (p₁.append p₂ hfs).finish = p₂.finish := by
  sorry

def reverse [Undirected G] (p : Path G) : Path G where
  toWalk := p.toWalk.reverse
  vNodup := by
    rw [Walk.reverse_vertices, List.nodup_reverse]
    exact p.vNodup

@[simp]
lemma reverse_start [Undirected G] (p : Path G) : (p.reverse).start = p.finish := rfl

@[simp]
lemma reverse_finish [Undirected G] (p : Path G) : (p.reverse).finish = p.start := p.toWalk.reverse_finish

end Path

structure Trail extends Walk G where
  eNodup : toWalk.edges.Nodup

structure Closed extends Walk G where
  startFinish : toWalk.start = toWalk.finish

structure Cycle extends Closed G where
  vNodup' : toWalk.vertices.tail.Nodup

structure Tour extends Closed G, Trail G

def Acyclic (G : Graph V E) : Prop := IsEmpty (Cycle G)

def conn (G : Graph V E) (u v : V) : Prop := ∃ w : Walk G, w.start = u ∧ w.finish = v

class connected (G : Graph V E) : Prop :=
  all_conn : ∀ u v : V, conn G u v

def connected_component (G : Graph V E) (v : V) : Set V := {u | G.conn u v}

def cut (G : Graph V E) (S : Finset E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

def bridge (G : Graph V E) (e : E) : Prop := G.cut {e}

def mincut (G : Graph V E) (S : Finset E) : Prop :=
  IsSmallest (G.cut ·) S

class Nconnected (G : Graph V E) (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.cut S
