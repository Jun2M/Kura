import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic
import Kura.Dep.List

open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β}
namespace Graph


inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (W : Walk α β) : Walk α β

namespace Walk
variable {w w₁ : Walk α β} {w₂ : Walk α β}

def start : Walk α β → α
| nil x => x
| cons x _ _ => x

def finish : Walk α β → α
| nil x => x
| cons _ _ w => w.finish

def ValidOn (w : Walk α β) (G : Graph α β) : Prop :=
  match w with
  | nil x => x ∈ G.V
  | cons x e w => G.IsBetween e x w.start ∧ w.ValidOn G

def vx : Walk α β → List α
| nil x => [x]
| cons x _e w => x :: w.vx

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vx

instance [DecidableEq α] : Decidable (x ∈ w) := by
  change Decidable (x ∈ w.vx)
  infer_instance

def edge : Walk α β → List β
| nil _ => []
| cons _ e w => e :: w.edge

def length : Walk α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

def concat : Walk α β → β → α → Walk α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

def reverse : Walk α β → Walk α β
| nil x => nil x
| cons x e w => w.reverse.concat e x

def startAt [DecidableEq α] (w : Walk α β) (u : α) (h : u ∈ w) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hin : u ∈ w
    then startAt w u hin
    else cons x e w

@[simp]
lemma cons_length : (cons x e w).length = w.length + 1 := rfl


lemma startAt_length_le [DecidableEq α] {w : Walk α β} (h : u ∈ w) : (startAt w u h).length ≤ w.length := by
  match w with
  | nil x => simp [startAt]
  | cons x e w =>
    simp only [startAt, cons_length]
    split_ifs with hin
    · have := startAt_length_le hin
      omega
    · simp

def dedup [DecidableEq α] : Walk α β → Walk α β
| nil x => nil x
| cons x e w =>
  if h : x ∈ w
  then by
    have := startAt_length_le h
    exact (startAt w x h).dedup
  else cons x e (dedup w)
termination_by w => w.length

@[simp] lemma nil_vx : (nil x : Walk α β).vx = [x] := rfl

@[simp] lemma nil_edge : (nil x : Walk α β).edge = [] := rfl

@[simp] lemma nil_length : (nil x : Walk α β).length = 0 := rfl

@[simp] lemma nil_start : (nil x : Walk α β).start = x := rfl

@[simp] lemma nil_finish : (nil x : Walk α β).finish = x := rfl

@[simp] lemma nil_validOn (hx : x ∈ G.V) : (nil x : Walk α β).ValidOn G := by
  simp [ValidOn, hx]

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_start : (cons x e w).start = x := rfl

@[simp] lemma cons_finish : (cons x e w).finish = w.finish := rfl

@[simp] lemma cons_validOn (hw : w.ValidOn G) (he : G.IsBetween e x w.start) :
  (cons x e w).ValidOn G := ⟨he, hw⟩

@[simp] lemma cons_validOn_iff : (cons x e w).ValidOn G ↔ G.IsBetween e x w.start ∧ w.ValidOn G :=
  ⟨fun h => h, fun h => h⟩

lemma vx_ne_nil : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

@[simp]
lemma mem_vx_nil_iff : x ∈ (nil u : Walk α β).vx ↔ x = u := by
  simp only [nil_vx, mem_cons, not_mem_nil, or_false]

@[simp]
lemma mem_vx_cons_iff : x ∈ (cons u e w).vx ↔ x = u ∨ x ∈ w.vx := by
  simp only [cons_vx, mem_cons]

@[simp]
lemma mem_edge_nil_iff : e ∈ (nil u : Walk α β).edge ↔ False := by
  simp only [nil_edge, mem_nil_iff]

@[simp]
lemma mem_edge_cons_iff : e ∈ (cons u e' w).edge ↔ e = e' ∨ e ∈ w.edge := by
  simp only [cons_edge, mem_cons]

/-- Properties of append operation -/
@[simp]
lemma append_vx : (append w₁ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_vx, ih]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil]
    simp

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (append w₁ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp [append, ih]

@[simp]
lemma append_length : (append w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_length, ih]
    omega

@[simp]
lemma nil_append : (nil x).append w = w := by
  induction w with
  | nil y => simp [append]
  | cons y e w ih => simp [append, ih]

@[simp]
lemma cons_append :
  (cons x e w₁).append w₂ = cons x e (w₁.append w₂) := rfl

@[simp]
lemma append_nil (h : w.finish = x) : w.append (nil x) = w := by
  induction w with
  | nil u => aesop
  | cons u e W ih =>
    rw [cons_finish] at h
    rw [cons_append, ih h]

@[simp]
lemma append_start (h : w₁.finish = w₂.start):
  (w₁.append w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp [append, ← h]
  | cons x e w ih => simp [append, ih]

@[simp]
lemma append_finish :
  (w₁.append w₂).finish = w₂.finish := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih => simp [append, ih]

lemma ValidOn.append (h : w₁.finish = w₂.start) (h₁ : w₁.ValidOn G) (h₂ : w₂.ValidOn G) :
  (append w₁ w₂).ValidOn G := by
  induction w₁ with
  | nil x => simpa
  | cons x e w₁ ih =>
    simp only [cons_finish] at h
    refine ⟨?_, by simp [ih h h₁.2]⟩
    convert h₁.1 using 1
    exact append_start h




end Walk

open Walk

variable {G H : Graph α β} {u v : α} {e : β} {w : Walk α β}

def IsBetween.Walk (_h : G.IsBetween e u v) : Walk α β := cons u e (nil v)

lemma IsBetween.walk_validOn (h : G.IsBetween e u v) : h.Walk.ValidOn G := by
  simp only [Walk, ValidOn, h.vx_mem_right, nil_start, h, cons_validOn]

@[simp] lemma IsBetween.Walk.start (h : G.IsBetween e u v): h.Walk.start = u := rfl

@[simp] lemma IsBetween.Walk.finish (h : G.IsBetween e u v): h.Walk.finish = v := rfl

@[simp] lemma IsBetween.Walk.vx (h : G.IsBetween e u v): h.Walk.vx = [u, v] := rfl

@[simp] lemma IsBetween.Walk.edge (h : G.IsBetween e u v): h.Walk.edge = [e] := rfl

@[simp] lemma IsBetween.Walk.length (h : G.IsBetween e u v): h.Walk.length = 1 := rfl

/-- Given a graph adjacency, we can create a walk of length 1 -/
lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidOn G ∧ W.length = 1 ∧ W.start = u ∧
    W.finish = v := by
  obtain ⟨e, he⟩ := h
  use he.Walk, he.walk_validOn
  simp only [IsBetween.Walk.length, IsBetween.Walk.start, IsBetween.Walk.finish, and_self]

/-- Given a reflexive adjacency, we can create a walk of length at most 1 -/
lemma reflAdj.exist_walk (h : G.reflAdj u v) : ∃ (W : Walk α β), W.ValidOn G ∧ W.length ≤ 1 ∧
    W.start = u ∧ W.finish = v := by
  obtain hadj | ⟨rfl, hx⟩ := h
  · obtain ⟨W, hW, hlength, hstart, hfinish⟩ := hadj.exist_walk
    use W, hW
    simp only [hlength, le_refl, hstart, hfinish, and_self]
  · use nil u
    constructor
    · simp [ValidOn, hx]
    · simp

lemma Connected.exist_walk (h : G.Connected u v) : ∃ (W : Walk α β), W.ValidOn G ∧
    W.start = u ∧ W.finish = v := by
  induction h with
  | single hradj =>
    obtain ⟨W, hW, hlength, hstart, hfinish⟩ := hradj.exist_walk
    use W
  | tail hconn hradj ih =>
    expose_names
    obtain ⟨W, hW, hstart, hfinish⟩ := ih
    obtain ⟨W', hW', hlength, hstart', hfinish'⟩ := hradj.exist_walk
    subst b c u
    use W.append W', ValidOn.append hstart'.symm hW hW'
    simp only [hstart', append_start, append_finish, and_self]

lemma Walk.connected_of_validOn (h : w.ValidOn G) : G.Connected w.start w.finish:= by
  induction w with
  | nil x => simpa only [nil_start, nil_finish, Connected.refl_iff]
  | cons x e w ih =>
    obtain ⟨H1, H2⟩ := h
    simp only [cons_start, cons_finish]
    exact H1.connected.trans (ih H2)

theorem Connected.iff_walk : G.Connected u v ↔ ∃ w : Walk α β, w.ValidOn G ∧ w.start = u ∧ w.finish = v := by
  constructor
  · exact fun a ↦ exist_walk a
  · rintro ⟨w, h1, rfl, rfl⟩
    exact connected_of_validOn h1

namespace Walk

/-- Properties of concat operation -/
@[simp]
lemma concat_vx {w : Walk α β} {e : β} {v : α} : (w.concat e v).vx = w.vx ++ [v] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_edge {w : Walk α β} {e : β} {v : α} : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_length {w : Walk α β} {e : β} {v : α} : (w.concat e v).length = w.length + 1 := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

/-- Properties of reverse operation -/
@[simp]
lemma reverse_vx {w : Walk α β} : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : Walk α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_length {w : Walk α β} : (reverse w).length = w.length := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

-- /-- Properties of dedup operation -/
-- lemma dedup_validOn [DecidableEq α] {w : Walk α β} (h : w.ValidOn G u v) : (dedup w).ValidOn G u v := sorry

-- lemma dedup_vx_nodup [DecidableEq α] (w : Walk α β) : (dedup w).vx.Nodup := sorry

-- /-- If there's a valid walk from u to v in graph G, then u and v are connected in G -/
-- lemma connected_of_validOn (h : w.ValidOn G u v) : G.Connected u v := sorry

-- lemma validOn_of_append (h₁ : w₁.ValidOn G u v) (h₂ : w₂.ValidOn G v z) :
--   (append w₁ w₂).ValidOn G u z := sorry

-- lemma validOn_of_concat (h : w.ValidOn G u v) (hbtw : G.IsBetween e v z) :
--   (w.concat e z).ValidOn G u z := sorry

-- lemma validOn_of_reverse (h : w.ValidOn G u v) : (reverse w).ValidOn G v u := sorry

-- /-- If the endpoints of a walk are connected in G, there exists a valid walk between them -/
-- lemma validOn_of_connected (h : G.Connected u v) : ∃ w : Walk α β, w.ValidOn G u v := sorry

-- /-- Two vertices are connected in a graph if and only if there exists a valid walk between them -/
-- @[simp]
-- lemma connected_iff_exists_validOn : G.Connected u v ↔ ∃ w : Walk α β, w.ValidOn G u v :=
--   ⟨validOn_of_connected, fun ⟨w', h⟩ => connected_of_validOn h⟩

/-- A subgraph inherits all valid walks -/
lemma ValidOn.le {w : Walk α β} (h : w.ValidOn G) (hle : G ≤ H) : w.ValidOn H := by
  match w with
  | nil x => exact vx_subset_of_le hle h
  | cons x e w =>
    obtain ⟨hbtw, hVd⟩ := h
    exact ⟨hbtw.le hle, hVd.le hle⟩

lemma ValidOn.mem_of_mem_vx {w : Walk α β} (h : w.ValidOn G) (hmem : x ∈ w.vx) :
    x ∈ G.V := by
  match w with
  | nil y =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hmem
    subst x
    exact h
  | cons y e w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : x = y ∨ x ∈ w.vx := by simpa using hmem
    · exact hbtw.vx_mem_left
    · exact hVd.mem_of_mem_vx h

lemma ValidOn.mem_of_mem_edge {w : Walk α β} (h : w.ValidOn G) (hmem : e ∈ w.edge) :
    e ∈ G.E := by
  match w with
  | nil x => simp at hmem
  | cons x e' w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : e = e' ∨ e ∈ w.edge := by simpa using hmem
    · exact hbtw.edge_mem
    · exact hVd.mem_of_mem_edge h

end Walk

lemma ValidOn.restrict (S : Set β) (w : Walk α β) (hVd : w.ValidOn G) (hS : ∀ e ∈ w.edge, e ∈ S) :
    w.ValidOn (G{S}) := by
  induction w with
  | nil x => exact hVd
  | cons x e w ih =>
    obtain ⟨hbtw, hVd⟩ := hVd
    specialize ih hVd ?_
    · rintro e' he'
      refine hS e' ?_
      simp [he']
    have he : e ∈ S := by
      apply hS
      simp
    simp [ih, hbtw, he]

lemma Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidOn G p C)
    (h : w.ValidOn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.start → p y = w.finish →
    ∃ w' : Walk α β, w'.ValidOn G ∧ w'.start = x ∧ w'.finish = y ∧
    {e | e ∈ w'.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  induction w with
  | nil u =>
    rintro x hx y hy hpx hpy
    simp only [nil_start, nil_finish] at hpx hpy
    subst u
    rw [hVd hy hx] at hpy
    obtain ⟨w, hwVd, rfl, rfl⟩ := hpy.symm.exist_walk
    use w, ?_, rfl, rfl
    · simp only [nil_edge, not_mem_nil, false_or, setOf_mem_eq]
      rintro e he
      have := hwVd.mem_of_mem_edge he
      exact Set.mem_of_mem_inter_right this
    · exact hwVd.le (restrict_le _ _)
  | cons u e W ih =>
    rintro x hx y hy hpx hpy
    have hw : (Walk.cons u e W).ValidOn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) := by
      apply ValidOn.restrict _ _ h ?_
      simp
    simp only [cons_start, cons_finish] at hpx hpy
    simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_isBetween, IsBetween, mem_setOf_eq,
      true_or, and_true] at hw
    simp only [cons_validOn_iff, IsBetween] at h
    obtain ⟨⟨z, rfl, a, ha, hbtw, he⟩, hVdW⟩ := hw
    obtain ⟨_B, hVdWp⟩ := h
    rw [hVd hx hbtw.vx_mem_left] at hpx
    obtain ⟨w, hVdw, rfl, rfl, hsu⟩ := ih hVdWp a hbtw.vx_mem_right y hy ha hpy
    obtain ⟨w', hw'Vd, rfl, rfl⟩ := hpx.exist_walk
    use w'.append (Walk.cons w'.finish e w), ?_, by simp, by simp
    · simp +contextual only [append_edge, cons_edge, mem_append, mem_cons, setOf_subset_setOf]
      rintro f (hfw' | rfl | hfw)
      · right
        have := hw'Vd.mem_of_mem_edge hfw'
        exact Set.mem_of_mem_inter_right this
      · tauto
      · obtain (h1 | h2) := hsu hfw <;> tauto
    · refine ValidOn.append (by simp) (hw'Vd.le (restrict_le _ _)) ?_
      simp [hVdw, hbtw]

lemma Contract.map_walk_of_walk {α' : Type*} {w : Walk α β} {p : α → α'} {C : Set β}
    (hVd : ValidOn G p C) (h : w.ValidOn G) : ∃ w' : Walk α' β, w'.ValidOn (G /[p] C) ∧
    w'.start = p w.start ∧ w'.finish = p w.finish ∧ {e | e ∈ w'.edge} ⊆ {e | e ∈ w.edge} := by
  induction w with
  | nil u =>
    use nil (p u), ?_, rfl, rfl, by simp
    use u, h
  | cons u e W ih =>
    obtain ⟨hbtw, hVdW⟩ := h
    obtain ⟨w', hw'Vd, hst, hfin, hsub⟩ := ih hVdW
    by_cases he : e ∈ C
    · have : p u = w'.start := by
        rw [hst, hVd hbtw.vx_mem_left hbtw.vx_mem_right]
        apply IsBetween.connected
        rw [restrict_isBetween]
        exact ⟨hbtw, he⟩
      use w', hw'Vd, this.symm, hfin
      simp only [cons_edge, mem_cons, setOf_subset_setOf]
      exact fun a a_1 ↦ Or.symm (Or.intro_left (a = e) (hsub a_1))
    · use (Walk.cons (p u) e w'), ?_, by simp, by simp [hfin]
      · simp only [cons_edge, mem_cons, setOf_subset_setOf, forall_eq_or_imp, true_or, true_and]
        rintro f hfw'
        right
        exact hsub hfw'
      · simp only [hw'Vd, cons_validOn_iff, IsBetween, and_true]
        use u, rfl, W.start, hst.symm, hbtw




/-- A path is a walk with no duplicate vertices -/
def Path (α β : Type*) [DecidableEq α] := {w : Walk α β // w.vx.Nodup}

namespace Path
variable [DecidableEq α] {p : Path α β}


/-- A path is valid on a graph if its underlying walk is valid -/
def ValidOn (p : Path α β) (G : Graph α β) : Prop := p.val.ValidOn G

def start (p : Path α β) : α := p.val.start

def finish (p : Path α β) : α := p.val.finish

/-- List of vertices in a path -/
def vx (p : Path α β) : List α := p.val.vx

/-- List of edges in a path -/
def edge (p : Path α β) : List β := p.val.edge

/-- Length of a path -/
def length (p : Path α β) : ℕ := p.val.length

/-- Create a nil path -/
def nil (x : α) : Path α β := ⟨Walk.nil x, by simp⟩

/-- Create a path from a single edge between two vertices -/
def IsBetween.path (hbtw : G.IsBetween e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.Walk, by simp [hne]⟩

/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {p : Path α β} (h : p.ValidOn G) (hle : G ≤ H) : p.ValidOn H :=
  Walk.ValidOn.le h hle

-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

section disjoint

variable {ι : Type*}

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : List (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (u v : α) (Ps : List (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

theorem Menger {α β : Type*} [DecidableEq α] (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V)
    (hv : v ∈ G.V) (hne : u ≠ v) (huv : ¬ G.Adj u v) (k : ℕ)
    (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
    ∃ Ps : List (Path α β), (Ps.length = k) ∧ (∀ p ∈ Ps, p.ValidOn G ∧ p.start = u ∧ p.finish = v) ∧ InternallyDisjoint u v Ps := by
  classical
  by_cases hk : k = 0
  · use [], by simp [hk], by simp, by simp [InternallyDisjoint]

  by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
  · obtain ⟨x, hux, hxv⟩ := hadj
    let G' := G[G.V \ {x}]
    have hG'le : G' ≤ G := induce_le G (by simp)
    have hu' : u ∈ G'.V := by
      simp only [induce_V, mem_diff, hu, mem_singleton_iff, true_and, G']
      rintro rfl
      exact huv hxv
    have hv' : v ∈ G'.V := by
      simp only [induce_V, mem_diff, hv, mem_singleton_iff, true_and, G']
      rintro rfl
      exact huv hux
    have huv' : ¬ G'.Adj u v := by
      contrapose! huv
      exact huv.of_Adj_induce
    obtain ⟨eux, heux⟩ := hux
    obtain ⟨exv, hexv⟩ := hxv
    let p : Path α β := ⟨((Walk.nil v).cons x exv).cons u eux, by
      simp [hne]
      by_contra h
      rw [← or_iff_not_and_not] at h
      obtain (rfl | rfl) := h
      · exact huv ⟨_, hexv⟩
      · exact huv ⟨_, heux⟩⟩
    have hp : p.ValidOn G := by
      simp only [ValidOn, cons_validOn_iff, nil_start, hexv, hv, nil_validOn, and_self, cons_start,
        heux, cons_validOn, G', p]
    have hpvx : p.vx = [u, x, v] := rfl
    have hG'Fin : G'.Finite := finite_of_le_finite hG'le
    have hG'term : (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard + (k - 1) < G.E.ncard + k := by
      sorry
    have := Menger G' u v hu' hv' hne huv' (k-1) ?_
    obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
    use p :: Ps, ?_, ?_
    · rintro y pi pj hpi hpj hyi hyj hpij
      by_cases hnepi : pi ≠ p ∧ pj ≠ p
      · have hpiPs : pi ∈ Ps := by simpa [hnepi.1] using hpi
        have hpjPs : pj ∈ Ps := by simpa [hnepi.2] using hpj
        exact hPs y pi pj hpiPs hpjPs hyi hyj hpij
      · wlog heqp : pi = p
        · apply this G u v hu hv hne huv k h hk x hG'le hu' hv' huv' eux heux exv hexv hp hpvx
            hG'Fin hG'term Ps hlen hPVd hPs y pj pi hpj hpi hyj hyi hpij.symm
            (by rw [and_comm] at hnepi; exact hnepi)
          push_neg at hnepi
          exact hnepi heqp
        subst pi
        simp only [hpvx, mem_cons, not_mem_nil, or_false] at hyi
        obtain rfl | rfl | rfl := hyi
        · left; rfl
        · rw [and_comm] at hnepi
          simp only [mem_cons, hpij.symm, false_or] at hpj
          obtain ⟨hPVd, hPstart, hPfinish⟩ := hPVd pj hpj
          have : y ∈ G'.V := hPVd.mem_of_mem_vx hyj
          simp [G'] at this
        · right; rfl
    · simp only [length_cons, hlen, G']
      omega
    · rintro p' hp'
      rw [List.mem_cons] at hp'
      obtain (rfl | hvalid) := hp'
      · use hp, rfl
        rfl
      · use (hPVd p' hvalid).1.le hG'le
        exact (hPVd p' hvalid).2
    · rintro s hsFin hSsepG'
      by_cases hxs : x ∈ s
      · refine (by omega : k - 1 ≤ k).trans (h s hsFin ?_)
        refine ⟨hSsepG'.not_mem_left, hSsepG'.not_mem_right, ?_⟩
        have := hSsepG'.not_connected
        simp only [induce_V, induce_induce_eq_induce_restrict, mem_diff, mem_singleton_iff,
          G'] at this
        convert this using 2
        rw [diff_diff, singleton_union, insert_eq_self.mpr hxs, eq_comm]
        apply subgraph_eq_induce
        simp +contextual only [mem_diff, setOf_subset_setOf, true_and, G']
        rintro e' h' x' hinc' rfl
        exact (h' x' hinc').2 hxs
      · specialize h (s ∪ {x}) (hsFin.union (by simp)) ?_
        · constructor
          · simp only [union_singleton, Set.mem_insert_iff, hSsepG'.not_mem_left, or_false, G']
            rintro rfl
            exact huv ⟨_, hexv⟩
          · simp only [union_singleton, Set.mem_insert_iff, hSsepG'.not_mem_right, or_false, G']
            rintro rfl
            exact huv ⟨_, heux⟩
          · convert hSsepG'.not_connected using 2
            simp only [union_singleton, induce_V, induce_induce_eq_induce_restrict, mem_diff,
              mem_singleton_iff, G']
            rw [diff_diff, singleton_union, eq_comm]
            apply subgraph_eq_induce
            simp +contextual only [mem_diff, Set.mem_insert_iff, not_or, setOf_subset_setOf,
              not_false_eq_true, and_self, implies_true, G']
        · rwa [ncard_union_eq (by simp [hxs]) hsFin, ncard_singleton, Nat.le_add_toss] at h
  · have : G.E.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro hE
      have := h ∅ (by simp) (by constructor <;> simp [hE, hne])
      simp only [ncard_empty, nonpos_iff_eq_zero] at this
      omega
    obtain ⟨e, he⟩ := this
    obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
    let G' := G{G.E \ {e}}
    have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
    by_cases h' : ∀ (S : Set α), S.Finite → G{G.E \ {e}}.IsVxSeparator u v S → k ≤ S.ncard
    · -- Deleting the edge did not decrease k, so get the paths from the smaller graph
      have hG'term : (G.E ∩ (G.E \ {e})).ncard + k < G.E.ncard + k := by
        simp only [restrict_E, add_lt_add_iff_right]
        apply Set.ncard_lt_ncard ?_ Finite.edge_fin
        refine inter_ssubset_left_iff.mpr ?_
        rintro hsu
        have := hsu he
        simp at this
      have := Menger (G{G.E \ {e}}) u v hu hv hne (by contrapose! huv; exact huv.of_Adj_restrict) k h'
      obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
      use Ps, hlen
      constructor
      · rintro p hp
        use (hPVd p hp).1.le hG'le
        exact (hPVd p hp).2
      · rintro pj hpj pi hpi x hx hx' hne
        refine hPs pj hpj pi hpi x ?_ ?_ hne
        · simpa using hx
        · simpa using hx'
    · -- Deleting the edge did decrease k, so contract instead
      simp only [not_forall, Classical.not_imp, not_le] at h'
      obtain ⟨S, hSFin, hSsep, hcard⟩ := h'
      let G'' := G /[hxy.contractFun] {e}
      have hG''term : (G.E \ {e}).ncard < G.E.ncard :=
        Set.ncard_diff_singleton_lt_of_mem he Finite.edge_fin
      have := Menger G'' (hxy.contractFun u) (hxy.contractFun v) ?_ ?_ ?_ ?_ k ?_
      obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
      sorry
      · exact Contract.map_mem hxy.contractFun {e} hu
      · exact Contract.map_mem hxy.contractFun {e} hv
      · simp only [IsBetween.contractFun, ne_eq]
        split_ifs with hueq hveq hveq
        · subst hueq hveq
          simp only [ne_eq, not_true_eq_false] at hne
        · subst hueq
          rintro rfl
          exact huv ⟨_, hxy.symm⟩
        · subst hveq
          rintro rfl
          exact huv ⟨_, hxy⟩
        · rintro rfl
          simp only [ne_eq, not_true_eq_false] at hne
      · sorry
      · sorry


      -- clear! G'
      -- have hneuv : (x ≠ u ∧ x ≠ v) ∨ (y ≠ u ∧ y ≠ v) := by
      --   by_contra h
      --   simp only [ne_eq, not_or, not_and, Decidable.not_not] at h
      --   by_cases hx : x = u <;> by_cases hy : y = u
      --   · subst x y
      --     sorry
      --   · have := h.2 hy
      --     subst x y
      --     sorry
      --   · have := h.1 hx
      --     subst x y
      --     sorry
      --   · have := h.1 hx
      --     have := h.2 hy
      --     subst x y

      --     sorry

      -- have hneuvy : y ≠ u ∧ y ≠ v := sorry
      -- -- · apply this G u v hu hv hne huv k h hk hadj e he y x hxy.symm hG'le h'
      -- --   · rwa [or_comm]
      -- --   · tauto
      -- obtain ⟨hyu, hyv⟩ := hneuvy
      -- clear hneuv
      -- simp only [not_forall, Classical.not_imp, not_le] at h'
      -- obtain ⟨S, hSFin, hSsep, hcard⟩ := h'
      -- have hxyne : x ≠ y := by sorry
      -- let G'' := G /[hxy.contractFun] {e}
      -- have hG''term : (G.E \ {e}).ncard < G.E.ncard :=
      --   Set.ncard_diff_singleton_lt_of_mem he Finite.edge_fin
      -- have hu'' : u ∈ G''.V := by
      --   use u, hu
      --   rw [hxy.contractFun_eq_self_iff hxyne]
      --   exact hyu.symm
      -- have hv'' : v ∈ G''.V := by
      --   use v, hv
      --   rw [hxy.contractFun_eq_self_iff hxyne]
      --   exact hyv.symm
      -- have := Menger G'' u v hu'' hv'' hne (by sorry) k ?_
      -- obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
      -- obtain ⟨pi, hpi, hpix⟩ : ∃ p ∈ Ps, x ∈ p.vx := by
      --   by_contra! h
      --   sorry

      -- sorry
      -- sorry

termination_by G.E.ncard + k


-- theorem Menger_zero {k : ℕ} {G : Graph α β} [G.Finite] (u v : α) (hk0 : k = 0) :
--     ∃ Ps : List (Path α β), (∀ p ∈ Ps, p.ValidOn G u v) ∧ InternallyDisjoint u v Ps := by
--   use []
--   simp [InternallyDisjoint]

-- theorem Menger_succ {k : ℕ} (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V) (hv : v ∈ G.V)
--     (hne : u ≠ v) (huv : ¬ G.Adj u v) (hkpos : 0 < k)
--     (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
--     ∃ Ps : List (Path α β), (∀ p ∈ Ps, p.ValidOn G u v) ∧ InternallyDisjoint u v Ps := by
--   classical
--   by_cases heuv : ∃ e : β, e ∈ G.E ∧ ¬ G.Inc u e ∧ ¬ G.Inc v e
--   · -- There exists an edge that is not incident to u or v
--     -- Therefore, we can use del/contract to reduce the problem to a smaller graph
--     obtain ⟨e, he, hnuinc, hnvinc⟩ := heuv
--     have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
--     by_cases h : ∀ (S : Set α), S.Finite → G{G.E \ {e}}.IsVxSeparator u v S → k ≤ S.ncard
--     · -- Deleting the edge did not decrease k, so get the paths from the smaller graph
--       have hG'term : (G.E ∩ (G.E \ {e})).ncard + k < G.E.ncard + k := by
--         simp only [restrict_E, add_lt_add_iff_right]
--         apply Set.ncard_lt_ncard ?_ Finite.edge_fin
--         refine inter_ssubset_left_iff.mpr ?_
--         rintro hsu
--         have := hsu he
--         simp at this
--       have := Menger_succ (G{G.E \ {e}}) u v hu hv hne (by contrapose! huv; exact huv.of_Adj_restrict) hkpos h
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       use Ps
--       constructor
--       · rintro p hp
--         exact (hPVd p hp).le hG'le
--       · intro pj hpj pi hpi x hx hx' hne
--         refine hPs pj hpj pi hpi x ?_ ?_ hne
--         · simpa using hx
--         · simpa using hx'
--     · -- Deleting the edge did decrease k, so contract instead
--       simp only [not_forall, Classical.not_imp, not_le] at h
--       obtain ⟨S, hSFin, hSsep, hcard⟩ := h
--       obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
--       let G'' := G /[hxy.contractFun] {e}
--       have hG''term : (G.E \ {e}).ncard < G.E.ncard :=
--         Set.ncard_diff_singleton_lt_of_mem he Finite.edge_fin
--       have hu'' : u ∈ G''.V := by
--         use u, hu, IsBetween.contractFun_eq_self_of_not_inc hxy hnuinc
--       have hv'' : v ∈ G''.V := by
--         use v, hv, IsBetween.contractFun_eq_self_of_not_inc hxy hnvinc
--       have := Menger_succ G'' u v hu'' hv'' hne (by sorry) hkpos ?_
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       obtain ⟨i, hi, hieq⟩ : ∃! p ∈ Ps, x ∈ p.vx := by
--         sorry
--       sorry
--       sorry
--   · -- No edge is not incident to u or v
--     -- So if there is no vertex adjacent to both u and v, then u and v are not connected
--     push_neg at heuv
--     by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
--     · -- There exists a vertex adjacent to both u and v
--       -- so get a path through that vertex
--       obtain ⟨x, hux, hxv⟩ := hadj
--       let G' := G[G.V \ {x}]
--       have hG'le : G' ≤ G := induce_le G Set.diff_subset
--       have hu' : u ∈ G'.V := by
--         simp only [induce_V, mem_diff, hu, mem_singleton_iff, true_and, G']
--         rintro rfl
--         exact huv hxv
--       have hv' : v ∈ G'.V := by
--         simp only [induce_V, mem_diff, hv, mem_singleton_iff, true_and, G']
--         rintro rfl
--         exact huv hux
--       have huv' : ¬ G'.Adj u v := by
--         contrapose! huv
--         exact huv.of_Adj_induce
--       have hG'Fin : G'.Finite := finite_of_le_finite hG'le
--       obtain ⟨eux, heux⟩ := hux
--       obtain ⟨exv, hexv⟩ := hxv
--       let p : Path α β := ⟨((Walk.nil v).cons x exv).cons u eux, by simp [hne]; sorry⟩
--       have hp : p.ValidOn G u v := ⟨rfl, heux, rfl, rfl, hexv⟩
--       have hpvx : p.vx = [u, x, v] := rfl
--       have hG'term : (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard + (k - 1) < G.E.ncard + k := by
--         suffices (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard ≤ G.E.ncard by omega
--         exact Set.ncard_le_ncard (fun e => by simp +contextual) Finite.edge_fin
--       have := Menger_succ G' (k := k-1) u v hu' hv' hne huv' sorry ?_
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       use p :: Ps, ?_
--       · rintro y pi pj hpi hpj hyi hyj hpij
--         by_cases h : pi ≠ p ∧ pj ≠ p
--         · sorry
--         · wlog h : pi = p
--           · sorry
--           subst pi
--           simp only [hpvx, mem_cons, not_mem_nil, or_false] at hyi
--           obtain rfl | rfl | rfl := hyi
--           · left; rfl
--           · sorry
--           · right; rfl
--       sorry
--       -- let Ps' : Fin k → G.Path u v := fun i ↦ Fin.cons sorry (fun i ↦ (Ps i).le hG'le) (i.cast (by sorry))
--       -- use Fin.cons sorry (fun i ↦ (Ps i).le hG'le)
--       sorry
--     · sorry
-- termination_by G.E.ncard + k


end disjoint

end Path

-- /-- Convert a walk to a path by deduplicating vertices -/
-- def Walk.toPath [DecidableEq α] (w : Walk α β) : Path α β :=
--   ⟨w.dedup, dedup_vx_nodup w⟩
