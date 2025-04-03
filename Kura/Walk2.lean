import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic
import Kura.Dep.List
import Mathlib.Data.Nat.PartENat

open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β}
namespace Graph


inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (W : Walk α β) : Walk α β

namespace Walk
variable {w w₁ : Walk α β} {w₂ : Walk α β}

def Nonempty : Walk α β → Prop
| nil _ => False
| cons _ _ _ => True

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

@[simp]
lemma mem_iff : (x ∈ w) = (x ∈ w.vx) := rfl

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

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

def endIf [DecidableEq α] {P : α → Prop} [DecidablePred P] (w : Walk α β) (h : ∃ u ∈ w.vx, P u) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hP : P x
    then nil x
    else cons x e (endIf w (by simpa only [cons_vx, mem_cons, exists_eq_or_imp, hP, false_or] using h))

@[simp] lemma nil_vx : (nil x : Walk α β).vx = [x] := rfl

@[simp] lemma nil_edge : (nil x : Walk α β).edge = [] := rfl

@[simp] lemma nil_length : (nil x : Walk α β).length = 0 := rfl

@[simp] lemma nil_start : (nil x : Walk α β).start = x := rfl

@[simp] lemma nil_finish : (nil x : Walk α β).finish = x := rfl

@[simp] lemma nil_validOn_iff : (nil x : Walk α β).ValidOn G ↔ x ∈ G.V := by
  simp only [ValidOn]

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_start : (cons x e w).start = x := rfl

@[simp] lemma cons_finish : (cons x e w).finish = w.finish := rfl

@[simp] lemma cons_validOn (hw : w.ValidOn G) (he : G.IsBetween e x w.start) :
  (cons x e w).ValidOn G := ⟨he, hw⟩

@[simp] lemma cons_validOn_iff : (cons x e w).ValidOn G ↔ G.IsBetween e x w.start ∧ w.ValidOn G :=
  ⟨fun h => h, fun h => h⟩

lemma Nonempty.exists_cons : w.Nonempty → ∃ x e w', w = cons x e w' := by
  induction w with
  | nil x => simp only [Nonempty, reduceCtorEq, exists_false, imp_self]
  | cons x e w ih => simp only [cons.injEq, exists_and_left, exists_eq', and_true, implies_true]

@[simp]
lemma Nonempty.not_nil : ¬ (nil x : Walk α β).Nonempty := by
  simp only [Nonempty, not_false_eq_true]

@[simp]
lemma Nonempty.cons_true : (cons x e w).Nonempty := by
  simp only [Nonempty]

@[simp]
lemma Nonempty.not_iff : ¬ w.Nonempty ↔ ∃ x, w = nil x := by
  match w with
  | nil x => simp only [not_nil, not_false_eq_true, nil.injEq, exists_eq']
  | cons x e w => simp only [Nonempty, not_true_eq_false, reduceCtorEq, exists_false]

lemma vx_ne_nil : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

@[simp]
lemma mem_vx_nil_iff : x ∈ (nil u : Walk α β) ↔ x = u := by
  simp only [mem_iff, nil_vx, mem_cons, not_mem_nil, or_false]

@[simp]
lemma mem_vx_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by
  simp only [mem_iff, cons_vx, mem_cons]

@[simp]
lemma mem_edge_nil_iff : e ∈ (nil u : Walk α β).edge ↔ False := by
  simp only [nil_edge, mem_nil_iff]

@[simp]
lemma mem_edge_cons_iff : e ∈ (cons u e' w).edge ↔ e = e' ∨ e ∈ w.edge := by
  simp only [cons_edge, mem_cons]

@[simp]
lemma start_vx_mem : w.start ∈ w.vx := by
  match w with
  | nil x => simp only [nil_vx, nil_start, mem_cons, not_mem_nil, or_false]
  | cons x e w => simp only [cons_vx, cons_start, mem_cons, true_or]

lemma start_eq_vx_head {w : Walk α β} : w.start = w.vx.head vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w => rfl

@[simp]
lemma finish_vx_mem {w : Walk α β} : w.finish ∈ w.vx := by
  match w with
  | nil x => simp
  | cons x e w =>
    simp only [cons_vx, cons_finish, mem_cons]
    right
    exact finish_vx_mem

lemma finish_eq_vx_getLast {w : Walk α β} : w.finish = w.vx.getLast vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w =>
    simp only [cons_finish, cons_vx, ne_eq, vx_ne_nil, not_false_eq_true, getLast_cons]
    apply finish_eq_vx_getLast

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

/-- Properties of append operation -/
@[simp]
lemma append_vx : (append w₁ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_vx, ih]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil]
    simp

lemma append_vx' (heq : w₁.finish = w₂.start) : (append w₁ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  induction w₁ with
  | nil x =>
    simp_all only [nil_finish, append_vx, nil_vx, dropLast_single, nil_append, cons_append]
    rw [start_eq_vx_head]
    exact (head_cons_tail w₂.vx vx_ne_nil).symm
  | cons x e w ih =>
    rw [append_vx] at ih
    simp only [cons_finish, append_vx, cons_vx, cons_append] at heq ⊢
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil]
    simp only [cons_append, List.cons.injEq, true_and]
    exact ih heq

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
lemma append_start_of_eq (h : w₁.finish = w₂.start):
  (w₁.append w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp [append, ← h]
  | cons x e w ih => simp [append, ih]

@[simp]
lemma append_start_of_nonempty (h : w₁.Nonempty) :
  (w₁.append w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at h
  | cons x e w ih => simp only [cons_append, cons_start]

@[simp]
lemma append_finish :
  (w₁.append w₂).finish = w₂.finish := by
  induction w₁ with
  | nil x => simp only [append]
  | cons x e w ih => simp only [append, cons_finish, ih]

lemma append_validOn (h : w₁.finish = w₂.start) (h₁ : w₁.ValidOn G) (h₂ : w₂.ValidOn G) :
  (append w₁ w₂).ValidOn G := by
  induction w₁ with
  | nil x => simpa
  | cons x e w₁ ih =>
    simp only [cons_finish] at h
    refine ⟨?_, by simp [ih h h₁.2]⟩
    convert h₁.1 using 1
    exact append_start_of_eq h

lemma append_left_validOn (h : w₁.finish = w₂.start) (hw₁ : w₁.Nonempty)
    (hVd : (append w₁ w₂).ValidOn G) : w₁.ValidOn G := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at hw₁
  | cons x e w ih =>
    simp only [cons_append, cons_validOn_iff] at hVd
    by_cases hNonempty : w.Nonempty
    · refine ⟨?_, ih h hNonempty hVd.2⟩
      convert hVd.1 using 1
      simp only [hNonempty, append_start_of_nonempty]
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, rfl⟩ := hNonempty
      simp only [cons_finish, nil_finish, nil_append, cons_validOn_iff, nil_start,
        nil_validOn_iff] at h hVd ⊢
      subst y
      refine ⟨hVd.1, hVd.2.mem_of_mem_vx start_vx_mem⟩

lemma ValidOn.append_right_validOn (hVd : (append w₁ w₂).ValidOn G) : w₂.ValidOn G := by
  induction w₁ with
  | nil x => simpa only [nil_append] using hVd
  | cons x e w ih =>
    simp only [cons_append, cons_validOn_iff] at hVd
    exact ih hVd.2

lemma ValidOn.finish_eq_start (hw₁ : w₁.Nonempty) (hVd₁ : w₁.ValidOn G) (hVd : (append w₁ w₂).ValidOn G) :
  w₁.finish = w₂.start := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at hw₁
  | cons x e w ih =>
    simp_all only [Nonempty.cons_true, cons_append, cons_validOn_iff, cons_finish, forall_const]
    by_cases hNonempty : w.Nonempty
    · simp_all only [forall_const, append_start_of_eq, true_and]
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, rfl⟩ := hNonempty
      simp_all only [Nonempty.not_nil, nil_finish, IsEmpty.forall_iff, nil_start, nil_validOn_iff,
        nil_append]
      exact hVd₁.1.eq_of_IsBetween hVd.1

end Walk

open Walk

variable {G H : Graph α β} {u v : α} {e : β} {w : Walk α β}

def IsBetween.walk (_h : G.IsBetween e u v) : Walk α β := cons u e (nil v)

lemma IsBetween.walk_validOn (h : G.IsBetween e u v) : h.walk.ValidOn G := by
  simp only [walk, ValidOn, h.vx_mem_right, nil_start, h, cons_validOn]

@[simp] lemma IsBetween.Walk.start (h : G.IsBetween e u v): h.walk.start = u := rfl

@[simp] lemma IsBetween.Walk.finish (h : G.IsBetween e u v): h.walk.finish = v := rfl

@[simp] lemma IsBetween.Walk.vx (h : G.IsBetween e u v): h.walk.vx = [u, v] := rfl

@[simp] lemma IsBetween.Walk.edge (h : G.IsBetween e u v): h.walk.edge = [e] := rfl

@[simp] lemma IsBetween.Walk.length (h : G.IsBetween e u v): h.walk.length = 1 := rfl

lemma IsBetween.mem_left_of_edge_mem_walk (h : G.IsBetween e u v) (he : e ∈ w.edge)
    (hVd : w.ValidOn G) : u ∈ w.vx := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons, cons_vx] at he ⊢
    obtain rfl | he' := he
    · obtain ⟨hbtw, hVd⟩ := hVd
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw.eq_or_eq_of_IsBetween h
      · left
        rfl
      · right
        exact start_vx_mem
    · right
      exact ih he' hVd.2

lemma IsBetween.mem_right_of_edge_mem_walk (h : G.IsBetween e u v) (he : e ∈ w.edge)
    (hVd : w.ValidOn G) : v ∈ w.vx := h.symm.mem_left_of_edge_mem_walk he hVd

/-- Given a graph adjacency, we can create a walk of length 1 -/
lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidOn G ∧ W.length = 1 ∧ W.start = u ∧
    W.finish = v := by
  obtain ⟨e, he⟩ := h
  use he.walk, he.walk_validOn
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
    use W.append W', append_validOn hstart'.symm hW hW'
    simp only [hstart', append_start_of_eq, append_finish, and_self]

lemma Walk.connected_of_validOn (h : w.ValidOn G) : G.Connected w.start w.finish := by
  induction w with
  | nil x => simpa only [nil_start, nil_finish, Connected.refl_iff]
  | cons x e w ih =>
    obtain ⟨H1, H2⟩ := h
    simp only [cons_start, cons_finish]
    exact H1.connected.trans (ih H2)

lemma Walk.connected_of_validOn_of_mem' (h : w.ValidOn G) (hx : u ∈ w.vx) :
    G.Connected u w.finish := by
  induction w generalizing u with
  | nil x =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst u
    simp only [nil_finish, Connected.refl_iff]
    exact h
  | cons x e w ih =>
    simp only [cons_vx, mem_cons] at hx
    obtain rfl | hx := hx
    · exact Connected.trans h.1.connected (ih h.2 (start_vx_mem))
    · exact ih h.2 hx

lemma Walk.connected_of_validOn_of_mem (h : w.ValidOn G) (hx : x ∈ w.vx) (hy : y ∈ w.vx) :
    G.Connected x y := by
  have hx' := Walk.connected_of_validOn_of_mem' h hx
  have hy' := Walk.connected_of_validOn_of_mem' h hy
  exact Connected.trans hx' hy'.symm

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


lemma eq_append_cons_of_edge_mem {w : Walk α β} {e : β} (he : e ∈ w.edge) :
    ∃ w₁ w₂ : Walk α β, w = w₁.append (cons w₁.finish e w₂) ∧ e ∉ w₁.edge := by
  induction w with
  | nil x => simp only [nil_edge, not_mem_nil] at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons] at he
    obtain rfl | he' := he
    · use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
    · by_cases h : e = e'
      · subst e'
        use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
      · obtain ⟨w₁, w₂, rfl, hnin⟩ := ih he'
        use cons x e' w₁, w₂, by simp only [cons_finish, cons_append]
        simp only [cons_edge, mem_cons, h, hnin, or_self, not_false_eq_true]

/-- A subgraph inherits all valid walks -/
lemma ValidOn.le {w : Walk α β} (h : w.ValidOn G) (hle : G ≤ H) : w.ValidOn H := by
  match w with
  | nil x => exact vx_subset_of_le hle h
  | cons x e w =>
    obtain ⟨hbtw, hVd⟩ := h
    exact ⟨hbtw.le hle, hVd.le hle⟩

lemma ValidOn.eq_nil_of_mem_isolated {w : Walk α β} {x : α} (hisol : G.Isolated x) (hmem : x ∈ w.vx)
    (h : w.ValidOn G) : w = nil x := by
  match w with
  | nil y => simp_all only [nil_vx, mem_cons, not_mem_nil, or_false]
  | cons y e w =>
    exfalso
    obtain ⟨hbtw, hVd⟩ := h
    simp only [cons_vx, mem_cons] at hmem
    obtain rfl | h := hmem
    · exact hisol e hbtw.inc_left
    · have := ValidOn.eq_nil_of_mem_isolated hisol h hVd
      subst w
      rw [nil_start] at hbtw
      exact hisol e hbtw.inc_right

lemma ValidOn.induce {U : Set α} (hVd : w.ValidOn G) (hU : ∀ x ∈ w.vx, x ∈ U) :
    w.ValidOn (G[U]) := by
  induction w with
  | nil x => simp only [ValidOn, induce_V, nil_vx, mem_cons, not_mem_nil, or_false, hU]
  | cons x e w ih =>
    obtain ⟨hbtw, hVd⟩ := hVd
    simp only [cons_vx, mem_cons, forall_eq_or_imp] at hU
    obtain ⟨hUx, hUw⟩ := hU
    refine ⟨?_, ih hVd hUw⟩
    simp only [induce_isBetween_iff, hbtw, true_and, hUx]
    exact hUw _ start_vx_mem

lemma ValidOn.restrict {S : Set β} (hVd : w.ValidOn G) (hS : ∀ e ∈ w.edge, e ∈ S) :
    w.ValidOn (G{S}) := by
  induction w with
  | nil x => exact hVd
  | cons x e w ih =>
    obtain ⟨hbtw, hVd⟩ := hVd
    specialize ih hVd ?_
    · rintro e' he'
      refine hS e' ?_
      simp only [cons_edge, mem_cons, he', or_true]
    have he : e ∈ S := by
      apply hS
      simp only [cons_edge, mem_cons, true_or]
    simp only [ih, restrict_isBetween, hbtw, he, and_self, cons_validOn]

lemma ValidOn.subgraph {U : Set α} {S : Set β} (hVd : w.ValidOn G) (hU : ∀ x ∈ w.vx, x ∈ U)
    (hS : ∀ e ∈ w.edge, e ∈ S) : w.ValidOn (G{S}[U]) := ValidOn.induce (ValidOn.restrict hVd hS) hU

end Walk
-- noncomputable def Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidOn G p C) (h : w.ValidOn (G /[p] C)) {x y : α} (hx : x ∈ G.V) (hy : y ∈ G.V)
--     (hpx : p x = w.start) (hpy : p y = w.finish) : Walk α β :=
--   match w with
--   | .nil u => ((hVd hx hy).mp <| hpx.trans hpy.symm).symm.exist_walk.choose
--   | .cons u e W => by
--     have hw : (Walk.cons u e W).ValidOn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) :=
--       ValidOn.restrict _ _ h (by simp)
--     simp only [cons_start, cons_finish] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_isBetween, IsBetween, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, IsBetween] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     exact w'.append (Walk.cons w'.finish e <| walk hVd h.2 hbtw.vx_mem_right hy ha hpy)

-- noncomputable def Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidOn G p C) (h : w.ValidOn (G /[p] C)) :
--     ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.start → p y = w.finish → Walk α β := by
--   induction w with
--   | nil u =>
--     rintro x hx y hy hpx hpy
--     simp only [nil_start, nil_finish] at hpx hpy
--     subst u
--     rw [hVd hy hx] at hpy
--     exact hpy.symm.exist_walk.choose
--   | cons u e W ih =>
--     rintro x hx y hy hpx hpy
--     have hw : (Walk.cons u e W).ValidOn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) := by
--       apply ValidOn.restrict _ _ h ?_
--       simp
--     simp only [cons_start, cons_finish] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_isBetween, IsBetween, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, IsBetween] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     exact w'.append (Walk.cons w'.finish e <| ih h.2 a hbtw.vx_mem_right y hy ha hpy)

-- lemma Contract.walk_validOn {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidOn G p C) (h : w.ValidOn (G /[p] C)) (hx : x ∈ G.V) (hy : y ∈ G.V)
--     (hpx : p x = w.start) (hpy : p y = w.finish) :
--     (Contract.walk hVd h hx hy hpx hpy).ValidOn G := by
--   match w with
--   | .nil u =>
--     unfold Contract.walk
--     obtain ⟨H1, H2, H3⟩ := ((hVd hx hy).mp <| hpx.trans hpy.symm).symm.exist_walk.choose_spec
--     exact H1.le (restrict_le _ _)
--   | .cons u e W =>
--     have hw : (Walk.cons u e W).ValidOn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) :=
--       ValidOn.restrict _ _ h (by simp)
--     simp only [cons_start, cons_finish] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_isBetween, IsBetween, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, IsBetween] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     unfold Contract.walk
--     -- change (w'.append (Walk.cons w'.finish e <| walk hVd h.2 hbtw.vx_mem_right hy ha hpy)).ValidOn G
--     sorry

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
      apply ValidOn.restrict h ?_
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
    · refine append_validOn (by simp) (hw'Vd.le (restrict_le _ _)) ?_
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

namespace Walk
variable [DecidableEq α]

@[simp]
lemma startAt_nil (hx : x ∈ (nil u : Walk α β).vx) : (nil u).startAt x hx = nil x := by
  simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
  subst u
  rfl

@[simp]
lemma startAt_start (hx : x ∈ w.vx) : (w.startAt x hx).start = x := by
  induction w with
  | nil u =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    exact hx.symm
  | cons u e W ih =>
    simp only [mem_iff, cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte]
      exact ih h
    · simp only [h, or_false, mem_iff, ↓reduceDIte, cons_start] at hx ⊢
      exact hx.symm

@[simp]
lemma startAt_finish (hx : x ∈ w.vx): (w.startAt x hx).finish = w.finish := by
  induction w with
  | nil u => rfl
  | cons u e W ih =>
    simp only [mem_iff, cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte]
      exact ih h
    · simp only [h, or_false, mem_iff, ↓reduceDIte, cons_finish]

@[simp]
lemma startAt_length (hx : x ∈ w.vx) : (w.startAt x hx).length ≤ w.length := by
  induction w with
  | nil u => simp only [startAt_nil, nil_length, le_refl]
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte, cons_length]
      have := ih h
      omega
    · simp only [mem_iff, h, ↓reduceDIte, cons_length, le_refl]

@[simp]
lemma startAt_sizeOf_le (hx : x ∈ w.vx) : sizeOf (w.startAt x hx) ≤ sizeOf w := by
  induction w with
  | nil u => simp only [startAt_nil, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte, cons.sizeOf_spec, sizeOf_default, add_zero]
      have := ih h
      omega
    · simp only [mem_iff, h, ↓reduceDIte, le_refl]

lemma startAt_validOn (hx : x ∈ w.vx) (hVd : w.ValidOn G) : (w.startAt x hx).ValidOn G := by
  induction w with
  | nil u => simpa [startAt]
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte]
      exact ih h hVd.2
    · simpa only [mem_iff, h, ↓reduceDIte]

lemma startAt_vx_count (hx : x ∈ w.vx) : (w.startAt x hx).vx.count x = 1 := by
  induction w with
  | nil u =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst u
    unfold startAt
    simp
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte]
      exact ih h
    · simp only [h, or_false, mem_iff, ↓reduceDIte, cons_vx] at hx ⊢
      subst u
      simp only [count_cons_self, add_eq_right]
      exact count_eq_zero.mpr h

lemma startAt_isSuffix (hx : x ∈ w.vx) :
    ∃ w' : Walk α β, w'.append (w.startAt x hx) = w := by
  induction w generalizing x with
  | nil u =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst u
    use nil x
    rfl
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte]
      obtain ⟨w', hw'⟩ := ih h
      use cons u e w'
      simp [hw']
    · simp only [h, or_false, mem_iff, ↓reduceDIte] at hx ⊢
      subst u
      use nil x
      rfl

lemma startAt_vx_sublist {w : Walk α β} {x : α} (hx : x ∈ w.vx) :
    (w.startAt x hx).vx ⊆ w.vx := by
  induction w with
  | nil u =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst u
    simp only [startAt_nil, nil_vx, List.Subset.refl]
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte, cons_vx]
      refine (ih h).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]
    · simp only [mem_iff, h, ↓reduceDIte, cons_vx, List.Subset.refl]

lemma startAt_edge_sublist {w : Walk α β} (hx : x ∈ w.vx) :
    (w.startAt x hx).edge ⊆ w.edge := by
  induction w with
  | nil u =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst u
    simp only [startAt_nil, nil_edge, List.Subset.refl]
  | cons u e W ih =>
    simp only [cons_vx, mem_cons] at hx
    unfold startAt
    by_cases h : x ∈ W.vx
    · simp only [mem_iff, h, ↓reduceDIte, cons_edge]
      refine (ih h).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]
    · simp only [mem_iff, h, ↓reduceDIte, cons_edge, List.Subset.refl]

lemma dedup_start (w : Walk α β) : w.dedup.start = w.start := by
  match w with
  | .nil u =>
    unfold dedup
    rfl
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · rw [cons_start, dedup_start (W.startAt u h), startAt_start]
    · rfl

lemma dedup_finish (w : Walk α β) : w.dedup.finish = w.finish := by
  match w with
  | .nil u =>
    unfold dedup
    rfl
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · rw [cons_finish, dedup_finish (W.startAt u h), startAt_finish]
    · simp only [cons_finish]
      exact dedup_finish W

lemma dedup_length (w : Walk α β) : w.dedup.length ≤ w.length := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_length, le_refl]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [cons_length, ge_iff_le]
      have := dedup_length (W.startAt u h)
      have := startAt_length_le h
      omega
    · simp only [cons_length, add_le_add_iff_right, ge_iff_le]
      exact dedup_length W

lemma dedup_sizeOf_le (w : Walk α β) : sizeOf w.dedup ≤ sizeOf w := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [cons.sizeOf_spec, sizeOf_default, add_zero]
      have := dedup_sizeOf_le (W.startAt u h)
      have := startAt_sizeOf_le h
      omega
    · simp only [cons.sizeOf_spec, sizeOf_default, add_zero, add_le_add_iff_left, ge_iff_le]
      exact dedup_sizeOf_le W

lemma dedup_validOn {w : Walk α β} (hVd : w.ValidOn G) : w.dedup.ValidOn G := by
  match w with
  | .nil u =>
    unfold dedup
    exact hVd
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [mem_iff, h, ↓reduceDIte]
      exact dedup_validOn (startAt_validOn h hVd.2)
    · simp only [dedup_validOn hVd.2, cons_validOn_iff, and_true]
      convert hVd.1 using 1
      exact dedup_start W

lemma dedup_vx_sublist {w : Walk α β} {x : α} (hx : x ∈ w.dedup.vx) : x ∈ w.vx := by
  match w with
  | .nil u =>
    unfold dedup at hx
    exact hx
  | .cons u e W =>
    unfold dedup at hx
    split_ifs at hx with h
    · simp only at hx
      exact mem_of_mem_tail <| startAt_vx_sublist h <| dedup_vx_sublist hx
    · simp only [cons_vx, mem_cons] at hx ⊢
      exact hx.imp (·) dedup_vx_sublist

lemma dedup_edge_sublist (w : Walk α β) : w.dedup.edge ⊆ w.edge := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_edge, List.Subset.refl]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [cons_edge]
      refine (dedup_edge_sublist (W.startAt u h)).trans ?_
      refine (startAt_edge_sublist h).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]
    · simp only [cons_edge, cons_subset, mem_cons, true_or, true_and]
      refine (dedup_edge_sublist W).trans ?_
      simp only [List.Subset.refl, subset_cons_of_subset]

lemma dedup_vx_nodup (w : Walk α β) : w.dedup.vx.Nodup := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_vx, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [mem_iff, h, ↓reduceDIte]
      exact dedup_vx_nodup (W.startAt u h)
    · simp only [cons_vx, nodup_cons, dedup_vx_nodup W, and_true]
      contrapose! h
      exact dedup_vx_sublist h

lemma dedup_edge_nodup {w : Walk α β} (hVd : w.ValidOn G) : w.dedup.edge.Nodup := by
  match w with
  | .nil u =>
    unfold dedup
    simp only [nil_edge, nodup_nil]
  | .cons u e W =>
    unfold dedup
    split_ifs with h
    · simp only [mem_iff, h, ↓reduceDIte]
      exact dedup_edge_nodup (startAt_validOn h hVd.2)
    · simp only [cons_edge, nodup_cons, dedup_edge_nodup hVd.2, and_true]
      obtain ⟨hne, hVd⟩ := hVd
      rintro he
      exact h <| hne.mem_left_of_edge_mem_walk (dedup_edge_sublist W he) hVd

variable {P : α → Prop} [DecidablePred P]

@[simp]
lemma endIf_nil {x : α} (h : ∃ u ∈ nil x, P u) : (nil x : Walk α β).endIf h = nil x := rfl

@[simp]
lemma endIf_cons {x : α} {e : β} {w : Walk α β} (h : ∃ u ∈ cons x e w, P u) :
    (cons x e w).endIf h = if hP : P x
    then nil x
    else cons x e (endIf w (by simp [hP] at h; exact h)) := by
  match w with
  | .nil u => rfl
  | .cons u e' w' => rfl

lemma endIf_start {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).start = w.start := by
  match w with
  | .nil x => simp only [endIf, nil_start]
  | .cons x e w =>
    simp only [endIf, cons_start]
    split_ifs <;> rfl

lemma endIf_finish {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    P (w.endIf h).finish := by
  match w with
  | .nil x => simpa only [endIf_nil, nil_finish, nil_vx, mem_cons, not_mem_nil, or_false,
    exists_eq_left] using h
  | .cons x e w =>
    rw [endIf]
    split_ifs with hPx
    · simpa only [nil_finish]
    · simp only [cons_vx, mem_cons, exists_eq_or_imp, hPx, false_or, cons_finish] at h ⊢
      exact endIf_finish h

lemma endIf_length {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).length ≤  w.length := by
  match w with
  | .nil x => simp only [endIf, nil_length, le_refl]
  | .cons x e w =>
    simp only [endIf, cons_length, ge_iff_le]
    split_ifs with h
    · simp only [nil_length, le_add_iff_nonneg_left, _root_.zero_le]
    · simp only [cons_length, add_le_add_iff_right]
      apply endIf_length

lemma endIf_sizeOf_le {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    sizeOf (w.endIf h) ≤ sizeOf w := by
  match w with
  | .nil x => simp only [endIf, nil.sizeOf_spec, sizeOf_default, add_zero, le_refl]
  | .cons x e w =>
    simp only [endIf, cons.sizeOf_spec, sizeOf_default, add_zero, ge_iff_le]
    split_ifs with h
    · simp only [nil.sizeOf_spec, sizeOf_default, add_zero, le_add_iff_nonneg_right,
      _root_.zero_le]
    · simp only [cons.sizeOf_spec, sizeOf_default, add_zero, add_le_add_iff_left]
      apply endIf_sizeOf_le

lemma endIf_validOn {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hVd : w.ValidOn G) :
    (w.endIf h).ValidOn G := by
  match w with
  | .nil x => simpa only [endIf, nil_validOn_iff]
  | .cons x e w =>
    simp only [endIf]
    split_ifs with hPx
    · rw [nil_validOn_iff]
      simp only [cons_validOn_iff] at hVd
      exact hVd.1.vx_mem_left
    · rw [cons_validOn_iff] at hVd ⊢
      refine ⟨?_, endIf_validOn _ hVd.2⟩
      convert hVd.1 using 1
      simp only [cons_vx, mem_cons, exists_eq_or_imp, hPx, false_or] at h
      exact endIf_start h

lemma endIf_vx_sublist {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).vx ⊆ w.vx := by
  match w with
  | .nil x => simp only [endIf, nil_vx, List.Subset.refl]
  | .cons x e w =>
    simp only [endIf, cons_vx]
    split_ifs with h
    · simp only [nil_vx, cons_subset, mem_cons, true_or, nil_subset, subset_cons_of_subset,
        and_self]
    · simp only [cons_vx, cons_subset, mem_cons, true_or, true_and]
      refine List.Subset.trans ?_ (List.subset_cons_self _ _)
      apply endIf_vx_sublist

lemma endIf_mem_vx {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hv : v ∈ (w.endIf h).vx):
    ¬ P v ∨ v = (w.endIf h).finish := by
  match w with
  | .nil x =>
    simp_all only [endIf_nil, mem_iff, nil_vx, mem_cons, not_mem_nil, or_false, nil_finish, or_true]
  | .cons x e w =>
    simp only [endIf_cons]
    split_ifs with hPx
    · simp only [endIf_cons, hPx, ↓reduceDIte, mem_iff, nil_vx, mem_cons, not_mem_nil,
      or_false] at hv
      subst v
      right
      rfl
    · simp_all only [endIf_cons, dite_false, mem_iff, cons_vx, mem_cons, cons_finish]
      obtain rfl | hvmem := hv
      · exact Or.inl hPx
      · simp only [cons_vx, mem_cons, exists_eq_or_imp, hPx, false_or] at h
        exact endIf_mem_vx h hvmem

lemma endIf_exists_isBetween_last {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hVd : w.ValidOn G)
    (hNonempty : (w.endIf h).Nonempty) : ∃ v ∈ (w.endIf h).vx, ¬ P v ∧ ∃ e, G.IsBetween e v (w.endIf h).finish := by
  match w with
  | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
  | .cons x e (nil y) =>
    simp_all only [cons_validOn_iff, nil_start, nil_validOn_iff, endIf_cons, endIf_nil, dite_eq_ite]
    split_ifs with hPx
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, true_or, ite_true, Nonempty.not_nil]
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, false_or, ite_false, Nonempty.cons_true, cons_finish, nil_finish,
      not_false_eq_true, true_and, not_true_eq_false, false_and]
      use e
      exact hVd.1
  | .cons x e (cons y e' w) =>
    unfold endIf
    split_ifs with hPx
    · simp_all only [cons_validOn_iff, cons_start, endIf_cons, dite_true, Nonempty.not_nil]
    · by_cases hPy : P y
      · simp_all only [cons_validOn_iff, cons_start, endIf_cons, dite_true, dite_eq_ite, ite_false,
        Nonempty.cons_true, cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, cons_finish,
        nil_finish, exists_eq_or_imp, not_false_eq_true, true_and, exists_eq_left,
        not_true_eq_false, false_and]
        use e
        exact hVd.1
      · let w' := cons y e' w
        rw [cons_finish, cons_vx]
        have h' : ∃ u ∈ w'.vx, P u := by
          change ∃ u ∈ (cons x e w').vx, P u at h
          simpa only [cons_vx, mem_cons, exists_eq_or_imp, hPx, false_or] using h
        have hNonempty' : (w'.endIf h').Nonempty := by
          simp only [endIf_cons, hPy, ↓reduceDIte, Nonempty.cons_true, w']
        obtain ⟨a, ha, hh⟩ := endIf_exists_isBetween_last (w := w') h' hVd.2 hNonempty'
        refine ⟨a, ?_, hh⟩
        rw [mem_cons]
        right
        exact ha

end Walk


noncomputable def dist {G : Graph α β} {u v : α} (h : G.Connected u v) : ℕ := by
  classical
  exact Nat.find (by
    obtain ⟨w, hwVd, rfl, rfl⟩ := h.exist_walk
    use w.length, w, hwVd
    : ∃ n, ∃ w : Walk α β, w.ValidOn G ∧ w.start = u ∧ w.finish = v ∧ w.length = n)



/-- A path is a walk with no duplicate vertices -/
def Path (α β : Type*) [DecidableEq α] := {w : Walk α β // w.vx.Nodup}

namespace Path
variable [DecidableEq α] {p : Path α β}

@[simp]
def ofWalk (w : Walk α β) : Path α β := ⟨w.dedup, w.dedup_vx_nodup⟩

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
def IsBetween.path (hbtw : G.IsBetween e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.walk, by simp [hne]⟩

/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {p : Path α β} (h : p.ValidOn G) (hle : G ≤ H) : p.ValidOn H :=
  Walk.ValidOn.le h hle

lemma of_prefix {p : Path α β} {w1 w2 : Walk α β} (h : p.val = w1.append w2)
    (heq : w1.finish = w2.start) : w1.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ _ := append_vx' heq
  rw [← h] at this
  have : w1.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_left w1.vx w2.vx.tail
  exact this.nodup p.prop

lemma of_suffix {p : Path α β} {w1 w2 : Walk α β} (h : p.val = w1.append w2) : w2.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ w2.vx := append_vx
  rw [← h] at this
  have : w2.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_right w1.vx.dropLast w2.vx
  exact this.nodup p.prop

def append (p q : Path α β) (hDisj : p.vx.dropLast.Disjoint q.vx) : Path α β :=
  ⟨p.val.append q.val, by
    rw [append_vx]
    refine List.Nodup.append ?_ q.prop hDisj
    exact p.prop.sublist (List.dropLast_sublist p.vx)⟩

lemma edge_not_isLoop {p : Path α β} (he : e ∈ p.edge) (hVd : p.ValidOn G) : ¬ G.IsLoop e := by
  intro hloop
  rw [IsLoop_iff_IsBetween] at hloop
  obtain ⟨x, hbtw⟩ := hloop
  obtain ⟨w₁, w₂, hw12, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.IsBetween e w₁.finish w₂.start := by
    simp only [ValidOn, hw12] at hVd
    obtain ⟨hbtw, H2⟩ := hVd.append_right_validOn
    exact hbtw
  have hNodup := hw12 ▸ p.prop
  simp only [append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hbtw.eq_or_eq_of_IsBetween hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

@[simp]
lemma IsBetween.path_vx (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).vx = [u, v] := by
  simp only [vx, path, IsBetween.Walk.vx]

end Path

variable [DecidableEq α]

lemma IsVxSetSeparator.path_inter {U : Set α} {S T : Set α} (hUsep : G.IsVxSetSeparator U S T)
    (p : Path α β) (hVd : p.ValidOn G) (hS : p.start ∈ S) (hT : p.finish ∈ T) :
    ∃ x ∈ p.vx, x ∈ U := by
  by_contra! hx
  have hVdU : p.ValidOn (G[G.V \ U]) := by
    refine ValidOn.induce hVd ?_
    rintro x hxp
    exact ⟨hVd.mem_of_mem_vx hxp, hx x hxp⟩
  exact hUsep p.val.start hS p.val.finish hT <| Walk.connected_of_validOn hVdU

lemma Contract.path {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidOn G p C)
    (h : w.ValidOn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.start → p y = w.finish →
    ∃ w' : Path α β, w'.ValidOn G ∧ w'.start = x ∧ w'.finish = y ∧
    {e | e ∈ w'.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use Path.ofWalk w', dedup_validOn hw'Vd, dedup_start w', dedup_finish w',
    Subset.trans (dedup_edge_sublist w') hsub

lemma Connected.iff_path : G.Connected u v ↔ ∃ p : Path α β, p.ValidOn G ∧ p.start = u ∧ p.finish = v := by
  rw [Connected.iff_walk]
  constructor
  · rintro ⟨w, hwVd, rfl, rfl⟩
    use Path.ofWalk w, dedup_validOn hwVd, dedup_start w, dedup_finish w
  · rintro ⟨p, hpVd, rfl, rfl⟩
    use p.val, hpVd, rfl
    rfl


-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

namespace Path
section disjoint

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi = pj


structure PathEnsemble (α β : Type*) [DecidableEq α] where
  Paths : Set (Path α β)
  Disj : Disjoint Paths

namespace PathEnsemble

def ValidOn (Ps : PathEnsemble α β) (G : Graph α β) := ∀ p ∈ Ps.Paths, p.ValidOn G

def StartSet (Ps : PathEnsemble α β) : Set α := Path.start '' Ps.Paths

def FinishSet (Ps : PathEnsemble α β) : Set α := Path.finish '' Ps.Paths

def VxSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.vx}

def EdgeSet (Ps : PathEnsemble α β) : Set β := {e | ∃ p ∈ Ps.Paths, e ∈ p.edge}

def InternalVsSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.vx.tail.dropLast}

lemma start_mem_StartSet {Ps : PathEnsemble α β} {p : Path α β} (hp : p ∈ Ps.Paths) :
    p.start ∈ Ps.StartSet := by
  use p, hp

lemma finish_mem_FinishSet {Ps : PathEnsemble α β} {p : Path α β} (hp : p ∈ Ps.Paths) :
    p.finish ∈ Ps.FinishSet := by
  use p, hp

lemma start_injOn (Ps : PathEnsemble α β) :
    InjOn Path.start Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hstart
  exact Ps.Disj _ _ _ hp₁ hp₂ start_vx_mem (by
    unfold Path.start at hstart
    exact hstart ▸ start_vx_mem)

lemma finish_injOn (Ps : PathEnsemble α β) :
    InjOn Path.finish Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hfinish
  exact Ps.Disj _ _ _ hp₁ hp₂ finish_vx_mem (by
    unfold Path.finish at hfinish
    exact hfinish ▸ finish_vx_mem)

lemma StartSet_union_InternalVsSet (Ps : PathEnsemble α β) :
    Ps.StartSet ∪ Ps.InternalVsSet = {x | ∃ p ∈ Ps.Paths, x ∈ p.vx.dropLast} := by
  sorry

lemma InternalVsSet_union_FinishSet (Ps : PathEnsemble α β) :
    Ps.InternalVsSet ∪ Ps.FinishSet = {x | ∃ p ∈ Ps.Paths, x ∈ p.vx.tail} := by
  sorry

lemma StartSet_union_InternalVsSet_union_FinishSet (Ps : PathEnsemble α β) :
    Ps.StartSet ∪ Ps.InternalVsSet ∪ Ps.FinishSet = Ps.VxSet := by
  sorry

lemma StartSet_InternalVsSet_disjoint (Ps : PathEnsemble α β) :
    _root_.Disjoint Ps.StartSet Ps.InternalVsSet := by
  sorry

lemma StartSet_FinishSet_disjoint (Ps : PathEnsemble α β) :
    _root_.Disjoint Ps.StartSet Ps.FinishSet := by
  sorry

lemma InternalVsSet_FinishSet_disjoint (Ps : PathEnsemble α β) :
    _root_.Disjoint Ps.InternalVsSet Ps.FinishSet := by
  sorry

lemma VxSet_diff_StartSet (Ps : PathEnsemble α β) :
    Ps.VxSet \ Ps.StartSet = Ps.InternalVsSet ∪ Ps.FinishSet := by
  sorry

lemma VxSet_diff_FinishSet (Ps : PathEnsemble α β) :
    Ps.VxSet \ Ps.FinishSet = Ps.StartSet ∪ Ps.InternalVsSet := by
  sorry

lemma VxSet_diff_InternalVsSet (Ps : PathEnsemble α β) :
    Ps.VxSet \ Ps.InternalVsSet = Ps.StartSet ∪ Ps.FinishSet := by
  sorry

lemma unique_path_start (Ps : PathEnsemble α β)  :
    ∀ x ∈ Ps.StartSet, ∃! p ∈ Ps.Paths, p.start = x := by
  rintro x hx
  obtain ⟨p, hp, rfl⟩ := hx
  use p, ⟨hp, rfl⟩
  rintro q ⟨hq, hstart⟩
  exact PathEnsemble.start_injOn Ps hq hp hstart

lemma unique_path_finish (Ps : PathEnsemble α β) :
    ∀ x ∈ Ps.FinishSet, ∃! p ∈ Ps.Paths, p.finish = x := by
  rintro x hx
  obtain ⟨p, hp, rfl⟩ := hx
  use p, ⟨hp, rfl⟩
  rintro q ⟨hq, hfinish⟩
  exact PathEnsemble.finish_injOn Ps hq hp hfinish

lemma StartSet_ncard {Ps : PathEnsemble α β} (hFin : Ps.Paths.Finite) :
    Ps.StartSet.ncard = Ps.Paths.ncard := by
  sorry

lemma FinishSet_ncard {Ps : PathEnsemble α β} (hFin : Ps.Paths.Finite) :
    Ps.FinishSet.ncard = Ps.Paths.ncard := by
  sorry

lemma ValidOn.le {Ps : PathEnsemble α β} {G G' : Graph α β} (h : G ≤ G') (hVd : Ps.ValidOn G) :
    Ps.ValidOn G' := by
  rintro p hp
  exact (hVd p hp).le h

def append (Ps₁ Ps₂ : PathEnsemble α β) (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) : PathEnsemble α β where
  Paths := by
    let f : ↑(Ps₁.VxSet ∩ Ps₂.VxSet) → Path α β := fun ⟨a, ha⟩ ↦
      (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose.append
      (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose ?_
    exact Set.range f
    · rintro b hbf hbg
      have h : b ∈ {x | ∃ p ∈ Ps₁.Paths, x ∈ p.vx.dropLast} := by
        use (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose, (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose_spec.1.1
      rw [← StartSet_union_InternalVsSet, ← VxSet_diff_FinishSet, ← h₁Finish, Set.diff_self_inter] at h
      obtain ⟨H1, H2⟩ := h
      have hb2 : b ∈ Ps₂.VxSet := by
        use (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose, (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose_spec.1.1
      exact H2 hb2
  Disj := by
    rintro x p q hp hq hxp hxq
    rw [Set.mem_range, Subtype.exists] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    have hw1a := (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose_spec
    have hw2a := (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose_spec
    have hw1b := (Ps₁.unique_path_finish b (h₁Finish ▸ hb)).choose_spec
    have hw2b := (Ps₂.unique_path_start b (h₂Start ▸ hb)).choose_spec
    simp only [vx, Path.append, append_vx, mem_append] at hxp hxq
    suffices h : a = b by
      subst b
      rfl
    obtain (hxp1 | hxp2) := hxp <;> obtain (hxq1 | hxq2) := hxq
    · have := Ps₁.Disj x _ _ hw1a.1.1 hw1b.1.1 (List.dropLast_subset _ hxp1) (List.dropLast_subset _ hxq1)
      rw [← hw1a.1.2, ← hw1b.1.2, this]
    · have h1 : x ∈ {x | ∃ p ∈ Ps₁.Paths, x ∈ p.vx.dropLast} := by
        use (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose, hw1a.1.1, hxp1
      rw [← StartSet_union_InternalVsSet, ← VxSet_diff_FinishSet, ← h₁Finish, Set.diff_self_inter] at h1
      obtain ⟨H1, H2⟩ := h1
      have h2 : x ∈ Ps₂.VxSet := by
        use (Ps₂.unique_path_start b (h₂Start ▸ hb)).choose, hw2b.1.1, hxq2
      exact False.elim (H2 h2)
    · have h1 : x ∈ {x | ∃ p ∈ Ps₁.Paths, x ∈ p.vx.dropLast} := by
        use (Ps₁.unique_path_finish b (h₁Finish ▸ hb)).choose, hw1b.1.1, hxq1
      rw [← StartSet_union_InternalVsSet, ← VxSet_diff_FinishSet, ← h₁Finish, Set.diff_self_inter] at h1
      obtain ⟨H1, H2⟩ := h1
      have h2 : x ∈ Ps₂.VxSet := by
        use (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose, hw2a.1.1, hxp2
      exact False.elim (H2 h2)
    · have := Ps₂.Disj x _ _ hw2a.1.1 hw2b.1.1 hxp2 hxq2
      rw [← hw2a.1.2, ← hw2b.1.2, this]


  -- Paths := by
  --   let f : Ps₁.Paths → Path α β := fun ⟨p, hp⟩ ↦ p.append (h p hp).choose ?_
  --   exact Set.range f
  --   rintro a hap haq
  --   obtain ⟨hmem2, hstart⟩ := (h p hp).choose_spec
  --   have haG := (hPs₁Vd p hp).mem_of_mem_vx (List.dropLast_subset p.vx hap)
  --   have haH := (hPs₂Vd (h p hp).choose hmem2).mem_of_mem_vx haq
  --   have hVxDisj := vx_disjoint_of_disjoint hGH (by simp [haG] : {a} ≤ _) (by simp [haH] : {a} ≤ _)
  --   simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at hVxDisj
  -- Disj := by
  --   rintro x p q hp hq hxp hxq
  --   simp only [Set.mem_range, Subtype.exists] at hp hq
  --   obtain ⟨w1, hw1, rfl⟩ := hp
  --   obtain ⟨w2, hw2, rfl⟩ := hq
  --   simp only [vx, Graph.Path.append, append_vx, mem_append] at hxp hxq
  --   suffices hw12 : w1 = w2 by
  --     subst w2
  --     rfl
  --   obtain (hxp1 | hxp2) := hxp <;> obtain (hxq1 | hxq2) := hxq
  --   · exact Ps₁.Disj _ _ _ hw1 hw2 (List.dropLast_subset w1.vx hxp1) (List.dropLast_subset w2.vx hxq1)
  --   · obtain ⟨hmem2, hstart⟩ := (h w2 hw2).choose_spec
  --     have haG := (hPs₁Vd w1 hw1).mem_of_mem_vx (List.dropLast_subset w1.vx hxp1)
  --     have haH := (hPs₂Vd (h w2 hw2).choose hmem2).mem_of_mem_vx hxq2
  --     have hVxDisj := vx_disjoint_of_disjoint hGH (by simp [haG] : {x} ≤ _) (by simp [haH] : {x} ≤ _)
  --     simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at hVxDisj
  --   · obtain ⟨hmem1, hstart⟩ := (h w1 hw1).choose_spec
  --     have haG := (hPs₁Vd w2 hw2).mem_of_mem_vx (List.dropLast_subset w2.vx hxq1)
  --     have haH := (hPs₂Vd (h w1 hw1).choose hmem1).mem_of_mem_vx hxp2
  --     have hVxDisj := vx_disjoint_of_disjoint hGH (by simp [haG] : {x} ≤ _) (by simp [haH] : {x} ≤ _)
  --     simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at hVxDisj
  --   · obtain ⟨hmem1, hstart1⟩ := (h w1 hw1).choose_spec
  --     obtain ⟨hmem2, hstart2⟩ := (h w2 hw2).choose_spec
  --     have := Ps₂.Disj _ _ _ hmem1 hmem2 hxp2 hxq2
  --     change (h w1 hw1).choose = (h w2 hw2).choose at this
  --     apply Ps₁.Disj _ _ _ hw1 hw2 finish_vx_mem
  --     unfold Path.finish at hstart1 hstart2
  --     rw [hstart1, this, ← hstart2]
  --     exact finish_vx_mem

lemma append_validOn {G : Graph α β} {Ps₁ Ps₂ : PathEnsemble α β}
    (hPs₁Vd : Ps₁.ValidOn G) (hPs₂Vd : Ps₂.ValidOn G) (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) : (Ps₁.append Ps₂ h₁Finish h₂Start).ValidOn G := by
  rintro p hp
  obtain ⟨⟨a, ha⟩, _, rfl⟩ := hp
  unfold Path.append Path.ValidOn
  let w1 := (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose
  let w2 := (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose
  have hw1a := (Ps₁.unique_path_finish a (h₁Finish ▸ ha)).choose_spec
  have hw2a := (Ps₂.unique_path_start a (h₂Start ▸ ha)).choose_spec
  change (w1.val.append w2.val).ValidOn G
  apply Walk.append_validOn
  · exact hw1a.1.2.trans hw2a.1.2.symm
  · exact hPs₁Vd _ hw1a.1.1
  · exact hPs₂Vd _ hw2a.1.1

lemma append_ncard_eq_left {Ps₁ Ps₂ : PathEnsemble α β} (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) (hFin : Ps₁.Paths.Finite) :
    (Ps₁.append Ps₂ h₁Finish h₂Start).Paths.ncard = Ps₁.Paths.ncard := by
  sorry

lemma append_ncard_eq_right {Ps₁ Ps₂ : PathEnsemble α β} (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) (hFin : Ps₂.Paths.Finite) :
    (Ps₁.append Ps₂ h₁Finish h₂Start).Paths.ncard = Ps₂.Paths.ncard := by
  sorry

lemma append_startSet {Ps₁ Ps₂ : PathEnsemble α β} (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ h₁Finish h₂Start).StartSet = Ps₁.StartSet := by
  sorry

lemma append_finishSet {Ps₁ Ps₂ : PathEnsemble α β} (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ h₁Finish h₂Start).FinishSet = Ps₂.FinishSet := by
  sorry

lemma append_VxSet {Ps₁ Ps₂ : PathEnsemble α β} (h₁Finish : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₁.FinishSet)
    (h₂Start : Ps₁.VxSet ∩ Ps₂.VxSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ h₁Finish h₂Start).VxSet = Ps₁.VxSet ∪ Ps₂.VxSet := by
  sorry

end PathEnsemble

end disjoint

end Path
