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
variable {w w₁ w₂ : Walk α β}

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
  | cons x e w => G.Inc₂ e x w.start ∧ w.ValidOn G

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

def dropLast : Walk α β → Walk α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (Walk α β) where
  append := append

def IsPrefix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w ++ w'

def IsSuffix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w' ++ w

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

@[simp] lemma nil_injective : Injective (nil : α → Walk α β) := by
  rintro x y h
  rwa [nil.injEq] at h

-- @[simp] lemma nil_inj : (nil x : Walk α β) = nil y ↔ x = y := by
--   rw [nil.injEq]

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_start : (cons x e w).start = x := rfl

@[simp] lemma cons_finish : (cons x e w).finish = w.finish := rfl

@[simp] lemma cons_validOn (hw : w.ValidOn G) (he : G.Inc₂ e x w.start) :
  (cons x e w).ValidOn G := ⟨he, hw⟩

@[simp] lemma cons_validOn_iff : (cons x e w).ValidOn G ↔ G.Inc₂ e x w.start ∧ w.ValidOn G :=
  ⟨fun h => h, fun h => h⟩

lemma ValidOn.of_cons (hw : (cons x e w).ValidOn G) : w.ValidOn G := by
  rw [cons_validOn_iff] at hw
  exact hw.2

lemma cons_vx_nodup (h : (cons x e w).vx.Nodup) : w.vx.Nodup := by
  simp only [cons_vx, nodup_cons] at h
  exact h.2

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


lemma Nonempty.exists_cons : w.Nonempty → ∃ x e w', w = cons x e w' := by
  induction w with
  | nil x => simp only [Nonempty, reduceCtorEq, exists_false, imp_self]
  | cons x e w ih => simp only [cons.injEq, exists_and_left, exists_eq', and_true, implies_true]

lemma Nonempty.iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  constructor
  · apply Nonempty.exists_cons
  · rintro ⟨x, e, w', rfl⟩
    simp only [Nonempty, cons.injEq, exists_and_left, exists_eq', and_true, implies_true]

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

@[simp]
lemma Nonempty.iff_length_pos : 0 < w.length ↔ w.Nonempty := by
  constructor
  · rintro hlen
    by_contra! h
    simp only [not_iff] at h
    obtain ⟨x, rfl⟩ := h
    simp at hlen
  · rw [Nonempty.iff_exists_cons]
    rintro ⟨x, e, w, rfl⟩
    simp only [cons_length, lt_add_iff_pos_left, add_pos_iff, lt_one_iff, pos_of_gt, or_true]

lemma start_eq_finish_of_not_nonempty (h : ¬ w.Nonempty) : w.start = w.finish := by
  match w with
  | nil x => simp only [nil_start, nil_finish]
  | cons x e w => simp only [Nonempty.cons_true, not_true_eq_false] at h

@[simp]
lemma start_eq_finish_iff (hnodup : w.vx.Nodup) : w.start = w.finish ↔ ¬ w.Nonempty := by
  match w with
  | .nil x => simp only [nil_start, nil_finish, Nonempty.not_nil, not_false_eq_true]
  | .cons x e w =>
    simp only [cons_vx, nodup_cons, cons_start, cons_finish, Nonempty.cons_true, not_true_eq_false,
      iff_false, ne_eq] at hnodup ⊢
    exact fun h => hnodup.1 (h ▸ finish_vx_mem)

@[simp]
lemma start_ne_finish_iff (hnodup : w.vx.Nodup) : w.start ≠ w.finish ↔ w.Nonempty :=
  (start_eq_finish_iff hnodup).not_left

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := by
  simp only [← append_notation, append]

@[simp]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := by
  simp only [← append_notation, append]

@[simp]
lemma append_vx : (w₁ ++ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih =>
    simp only [append_notation, append, cons_vx]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil, List.cons_append]
    simpa

lemma append_vx' {w₁ w₂ : Walk α β} (heq : w₁.finish = w₂.start) :
    (w₁ ++ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  match w₁ with
  | .nil x =>
    simp_all only [nil_finish, append_vx, nil_vx, dropLast_single, nil_append, cons_append]
    rw [start_eq_vx_head]
    exact (head_cons_tail w₂.vx vx_ne_nil).symm
  | .cons x e w =>
    simp only [cons_finish, cons_append, cons_vx, List.cons_append, List.cons.injEq,
      true_and] at heq ⊢
    exact append_vx' heq

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_edge, List.nil_append]
  | cons x e w ih => simp only [cons_append, cons_edge, ih, List.cons_append]

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_length, zero_add]
  | cons x e w ih =>
    simp only [cons_append, cons_length, ih]
    omega

@[simp]
lemma append_nil (h : w.finish = x) : w ++ (nil x) = w := by
  induction w with
  | nil u => aesop
  | cons u e W ih =>
    rw [cons_finish] at h
    rw [cons_append, ih h]

@[simp]
lemma append_start_of_eq (h : w₁.finish = w₂.start):
  (w₁ ++ w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp only [nil_append, ← h, nil_finish, nil_start]
  | cons x e w ih => simp only [cons_append, cons_start]

@[simp]
lemma append_start_of_nonempty (h : w₁.Nonempty) :
  (w₁ ++ w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at h
  | cons x e w ih => simp only [cons_append, cons_start]

@[simp]
lemma append_finish :
  (w₁ ++ w₂).finish = w₂.finish := by
  induction w₁ with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, cons_finish, ih]

lemma append_assoc (w1 w2 w3 : Walk α β) : (w1 ++ w2) ++ w3 = w1 ++ (w2 ++ w3) := by
  induction w1 with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, ih]

lemma append_right_injective : Injective (w ++ ·) := by
  rintro w₁ w₂ h
  induction w with
  | nil x => simpa only [nil_append] using h
  | cons x e w ih =>
    simp only [cons_append, cons.injEq, true_and] at h
    exact ih h

@[simp]
lemma append_right_inj : w ++ w₁ = w ++ w₂ ↔ w₁ = w₂ := by
  constructor
  · apply append_right_injective
  · rintro rfl
    rfl

@[simp]
lemma append_right_eq_self : w ++ w₁ = w ↔ w₁ = nil w.finish := by
  induction w with
  | nil x => simp only [nil_append, nil_finish]
  | cons x e w ih => simpa only [cons_append, cons.injEq, true_and, cons_finish]

@[simp]
lemma append_left_eq_self : w₁ ++ w = w ↔ ¬ w₁.Nonempty := by
  induction w₁ with
  | nil x => simp only [nil_append, Nonempty.not_nil, not_false_eq_true]
  | cons x e w ih =>
    simp only [cons_append, Nonempty.cons_true, not_true_eq_false, iff_false]
    intro hcons
    apply_fun length at hcons
    simp only [cons_length, append_length] at hcons
    omega

@[simp]
lemma append_eq_nil_iff : w₁ ++ w₂ = nil x ↔ (∃ y, w₁ = nil y) ∧ w₂ = nil x := by
  induction w₁ with
  | nil y => simp only [nil_append, nil.injEq, exists_eq', true_and]
  | cons y e w ih => simp only [cons_append, reduceCtorEq, exists_false, false_and]

lemma append_validOn (h : w₁.finish = w₂.start) (h₁ : w₁.ValidOn G) (h₂ : w₂.ValidOn G) :
  (w₁ ++ w₂).ValidOn G := by
  induction w₁ with
  | nil x => simpa
  | cons x e w₁ ih =>
    simp only [cons_finish] at h
    refine ⟨?_, by simp [ih h h₁.2]⟩
    convert h₁.1 using 1
    exact append_start_of_eq h

lemma ValidOn.append_left_validOn (h : w₁.finish = w₂.start) (hw₁ : w₁.Nonempty)
    (hVd : (w₁ ++ w₂).ValidOn G) : w₁.ValidOn G := by
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

lemma ValidOn.append_right_validOn (hVd : (w₁ ++ w₂).ValidOn G) : w₂.ValidOn G := by
  induction w₁ with
  | nil x => simpa only [nil_append] using hVd
  | cons x e w ih =>
    simp only [cons_append, cons_validOn_iff] at hVd
    exact ih hVd.2

lemma ValidOn.finish_eq_start (hw₁ : w₁.Nonempty) (hVd₁ : w₁.ValidOn G) (hVd : (w₁ ++ w₂).ValidOn G) :
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
      exact hVd₁.1.eq_of_inc₂ hVd.1

/- Properties of IsPrefix -/
namespace IsPrefix

instance instIsPrefixPreorder: IsPreorder (Walk α β) IsPrefix where
  refl w := ⟨nil w.finish, by simp [append_nil rfl]⟩
  trans w1 w2 w3 h12 h23 := by
    obtain ⟨w12, hw12⟩ := h12
    obtain ⟨w23, hw23⟩ := h23
    use w23 ++ w12
    rw [← append_assoc, ← hw23, ← hw12]

end IsPrefix

namespace IsSuffix

instance instIsSuffixPartialOrder: IsPartialOrder (Walk α β) IsSuffix where
  refl w := ⟨nil w.start, by simp [append_nil rfl]⟩
  trans w1 w2 w3 h12 h23 := by
    obtain ⟨w12, hw12⟩ := h12
    obtain ⟨w23, hw23⟩ := h23
    use w12 ++ w23
    rw [append_assoc, ← hw23, ← hw12]
  antisymm w1 w2 h12 h21 := by
    obtain ⟨w21, hw21⟩ := h21
    obtain ⟨w12, hw12⟩ := h12
    have := hw12 ▸ hw21 ▸ hw12
    rw [append_right_inj, ← append_assoc, eq_comm, append_left_eq_self] at this
    simp only [Nonempty.not_iff, append_eq_nil_iff, exists_and_left] at this
    obtain ⟨⟨y, rfl⟩, x, rfl⟩ := this
    simpa using hw12

end IsSuffix
end Walk

open Walk

variable {G H : Graph α β} {u v : α} {e : β} {w : Walk α β}

def Inc₂.walk (_h : G.Inc₂ e u v) : Walk α β := cons u e (nil v)

lemma Inc₂.walk_validOn (h : G.Inc₂ e u v) : h.walk.ValidOn G := by
  simp only [walk, ValidOn, h.vx_mem_right, nil_start, h, cons_validOn]

@[simp] lemma Inc₂.Walk.start (h : G.Inc₂ e u v): h.walk.start = u := rfl

@[simp] lemma Inc₂.Walk.finish (h : G.Inc₂ e u v): h.walk.finish = v := rfl

@[simp] lemma Inc₂.Walk.vx (h : G.Inc₂ e u v): h.walk.vx = [u, v] := rfl

@[simp] lemma Inc₂.Walk.edge (h : G.Inc₂ e u v): h.walk.edge = [e] := rfl

@[simp] lemma Inc₂.Walk.length (h : G.Inc₂ e u v): h.walk.length = 1 := rfl

lemma Inc₂.mem_left_of_edge_mem_walk (h : G.Inc₂ e u v) (he : e ∈ w.edge)
    (hVd : w.ValidOn G) : u ∈ w.vx := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons, cons_vx] at he ⊢
    obtain rfl | he' := he
    · obtain ⟨hbtw, hVd⟩ := hVd
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw.eq_or_eq_of_inc₂ h
      · left
        rfl
      · right
        exact start_vx_mem
    · right
      exact ih he' hVd.2

lemma Inc₂.mem_right_of_edge_mem_walk (h : G.Inc₂ e u v) (he : e ∈ w.edge)
    (hVd : w.ValidOn G) : v ∈ w.vx := h.symm.mem_left_of_edge_mem_walk he hVd

/-- Given a graph adjacency, we can create a walk of length 1 -/
lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidOn G ∧ W.length = 1 ∧ W.start = u ∧
    W.finish = v := by
  obtain ⟨e, he⟩ := h
  use he.walk, he.walk_validOn
  simp only [Inc₂.Walk.length, Inc₂.Walk.start, Inc₂.Walk.finish, and_self]

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
    use W ++ W', append_validOn hstart'.symm hW hW'
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

/-- Properties of dropLast operation -/
@[simp]
lemma dropLast_nil : (nil x : Walk α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_nil : (cons x e (nil y) : Walk α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_cons :
  (cons x e (cons y e' w) : Walk α β).dropLast = cons x e ((cons y e' w).dropLast) := rfl

@[simp]
lemma dropLast_start {w : Walk α β} (h : w.Nonempty) : (w.dropLast).start = w.start := by
  match w with
  | .nil x => simp at h
  | .cons x e (.nil y) => simp
  | .cons x e (cons y e' w) => simp

@[simp]
lemma dropLast_vx {w : Walk α β} (h : w.Nonempty) : (w.dropLast).vx = w.vx.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_vx, cons_vx, dropLast_cons₂, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_vx, dropLast_cons₂, List.cons.injEq, true_and]
    rw [← cons_vx (e := e')]
    apply dropLast_vx (by simp)

@[simp]
lemma dropLast_edge {w : Walk α β} (h : w.Nonempty) : (w.dropLast).edge = w.edge.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_edge, cons_edge, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_edge, dropLast_cons₂, List.cons.injEq, true_and]
    exact dropLast_edge (by simp)

lemma dropLast_validOn {w : Walk α β} (hVd : w.ValidOn G) :
    (w.dropLast).ValidOn G := by
  match w with
  | .nil x => simp only [dropLast, hVd]
  | .cons x e (.nil y) =>
    simp only [cons_validOn_iff, nil_start, nil_validOn_iff] at hVd
    exact hVd.1.vx_mem_left
  | .cons x e (cons y e' w) =>
    rw [dropLast, cons_validOn_iff, dropLast_start (by simp)]
    rw [cons_validOn_iff] at hVd
    refine ⟨hVd.1, ?_⟩
    exact dropLast_validOn hVd.2

lemma mem_dropLast_or_finish_of_mem {w : Walk α β} (hu : u ∈ w.vx) :
    u ∈ w.dropLast ∨ u = w.finish := by
  match w with
  | .nil x => simpa only [nil_finish, dropLast_nil, mem_iff, nil_vx, mem_cons, not_mem_nil,
    or_false, or_self] using hu
  | .cons x e (.nil y) =>
    simp only [mem_iff, cons_vx, nil_vx, mem_cons, not_mem_nil, or_false] at hu
    obtain rfl | rfl := hu <;> simp only [cons_finish, nil_finish, dropLast_cons_nil, mem_iff,
      nil_vx, mem_cons, not_mem_nil, or_false, true_or, or_true]
  | .cons x e (cons y e' w) =>
    simp only [mem_iff, cons_vx, mem_cons] at hu
    obtain rfl | rfl | hu := hu
    · simp
    · simp only [cons_finish, dropLast_cons_cons, mem_iff, cons_vx, Nonempty.cons_true,
      dropLast_vx, mem_cons]
      have := mem_dropLast_or_finish_of_mem (by simp : u ∈ (cons u e' w))
      simp only [cons_finish, mem_iff, Nonempty.cons_true, dropLast_vx, cons_vx] at this
      tauto
    · simp only [cons_finish, dropLast_cons_cons, mem_iff, cons_vx, Nonempty.cons_true,
      dropLast_vx, mem_cons]
      have := mem_dropLast_or_finish_of_mem (by simp [hu] : u ∈ (cons y e' w))
      simp only [cons_finish, mem_iff, Nonempty.cons_true, dropLast_vx, cons_vx] at this
      tauto

lemma mem_of_mem_dropLast {w : Walk α β} (h : u ∈ w.dropLast.vx) : u ∈ w.vx := by
  match w with
  | .nil x => simpa only [nil_vx, mem_cons, not_mem_nil, or_false, dropLast_nil] using h
  | .cons x e (.nil y) => simp_all only [dropLast_cons_nil, nil_vx, mem_cons, not_mem_nil, or_false,
    cons_vx, true_or]
  | .cons x e (cons y e' w) =>
    simp only [dropLast_cons_cons, cons_vx, Nonempty.cons_true, dropLast_vx, mem_cons] at h ⊢
    obtain rfl | h := h
    · left
      rfl
    · have := mem_of_mem_dropLast (w := cons y e' w) (by simpa only [Nonempty.cons_true,
      dropLast_vx, cons_vx])
      right
      simpa only [cons_vx, mem_cons] using this

lemma mem_dropLast_or_finish_of_mem_iff :
    u ∈ w.dropLast.vx ∨ u = w.finish ↔ u ∈ w.vx := by
  refine ⟨?_, mem_dropLast_or_finish_of_mem⟩
  rintro (h | rfl)
  · exact mem_of_mem_dropLast h
  · exact finish_vx_mem

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



lemma eq_append_of_vx_mem {w : Walk α β} {u : α} (hmem : u ∈ w.vx) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ w₂ ∧ w₁.finish = u ∧ w₂.start = u := by
  induction w with
  | nil x =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hmem
    subst u
    exact ⟨nil x, nil x, rfl, rfl, rfl⟩
  | cons x e w ih =>
    simp only [cons_vx, mem_cons] at hmem
    obtain rfl | h := hmem
    · exact ⟨nil u, cons u e w, rfl, rfl, rfl⟩
    · obtain ⟨w₁, w₂, rfl, hfin, hstart⟩ := ih h
      use cons x e w₁, w₂
      simp only [cons_append, cons_finish, hfin, hstart, and_self]

lemma eq_append_cons_of_edge_mem {w : Walk α β} {e : β} (he : e ∈ w.edge) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ cons w₁.finish e w₂ ∧ e ∉ w₁.edge := by
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
    simp only [induce_inc₂_iff, hbtw, true_and, hUx]
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
    simp only [ih, restrict_inc₂, hbtw, he, and_self, cons_validOn]

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
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, Inc₂] at h
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
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, Inc₂] at h
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
--     simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validOn_iff, Inc₂] at h
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
    simp only [cons_edge, mem_cons, cons_validOn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
      true_or, and_true] at hw
    simp only [cons_validOn_iff, Inc₂] at h
    obtain ⟨⟨z, rfl, a, ha, hbtw, he⟩, hVdW⟩ := hw
    obtain ⟨_B, hVdWp⟩ := h
    rw [hVd hx hbtw.vx_mem_left] at hpx
    obtain ⟨w, hVdw, rfl, rfl, hsu⟩ := ih hVdWp a hbtw.vx_mem_right y hy ha hpy
    obtain ⟨w', hw'Vd, rfl, rfl⟩ := hpx.exist_walk
    use w' ++ (cons w'.finish e w), ?_, by simp, by simp
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
        apply Inc₂.connected
        rw [restrict_inc₂]
        exact ⟨hbtw, he⟩
      use w', hw'Vd, this.symm, hfin
      simp only [cons_edge, mem_cons, setOf_subset_setOf]
      exact fun a a_1 ↦ Or.symm (Or.intro_left (a = e) (hsub a_1))
    · use (Walk.cons (p u) e w'), ?_, by simp, by simp [hfin]
      · simp only [cons_edge, mem_cons, setOf_subset_setOf, forall_eq_or_imp, true_or, true_and]
        rintro f hfw'
        right
        exact hsub hfw'
      · simp only [hw'Vd, cons_validOn_iff, Inc₂, and_true]
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
    ∃ w' : Walk α β, w' ++ (w.startAt x hx) = w := by
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

/- Properties of `endIf` -/

@[simp]
lemma endIf_nil {x : α} (h : ∃ u ∈ nil x, P u) : (nil x : Walk α β).endIf h = nil x := rfl

lemma endIf_eq_nil {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hP : P w.start) :
    w.endIf h = nil w.start := by
  match w with
  | .nil u => rfl
  | .cons u e w' => simpa only [endIf, cons_start, dite_eq_left_iff, reduceCtorEq, imp_false,
    not_not] using hP

  @[simp]
lemma endIf_cons {x : α} {e : β} {w : Walk α β} (h : ∃ u ∈ cons x e w, P u) :
    (cons x e w).endIf h = if hP : P x
    then nil x
    else cons x e (endIf w (by simp [hP] at h; exact h)) := by
  match w with
  | .nil u => rfl
  | .cons u e' w' => rfl

@[simp]
lemma endIf_start {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).start = w.start := by
  match w with
  | .nil x => simp only [endIf, nil_start]
  | .cons x e w =>
    simp only [endIf, cons_start]
    split_ifs <;> rfl

@[simp]
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

@[simp]
lemma endIf_eq_nil_iff {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    w.endIf h = nil w.start ↔ P w.start := by
  constructor
  · rintro heq
    have := heq ▸ endIf_finish h
    simpa only [nil_finish]
  · exact fun a ↦ endIf_eq_nil h a

@[simp]
lemma endIf_nonempty_iff {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).Nonempty ↔ ¬ P w.start := by
  rw [iff_not_comm]
  convert (endIf_eq_nil_iff h).symm
  simp only [Nonempty.not_iff, endIf_eq_nil_iff]
  constructor <;> rintro h'
  · obtain ⟨x, hx⟩ := h'
    have := hx ▸ endIf_start h
    rw [← this]
    have := hx ▸ endIf_finish h
    simpa using this
  · use w.start
    simp only [endIf_eq_nil_iff, h']

@[simp]
lemma endIf_length {w : Walk α β} (h : ∃ u ∈ w.vx, P u) :
    (w.endIf h).length ≤ w.length := by
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

lemma endIf_dropLast_mem_vx {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hNonempty : (w.endIf h).Nonempty)
    (hu : u ∈ (w.endIf h).dropLast.vx) : ¬ P u := by
  match w with
  | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
  | .cons x e (nil y) =>
    simp_all only [endIf_cons, endIf_nil, dite_eq_ite, dropLast_vx]
    split_ifs at hu with hPx
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, true_or, ite_true, Nonempty.not_nil]
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, false_or, ite_false, Nonempty.cons_true, dropLast_cons₂, dropLast_single,
      not_false_eq_true]
  | .cons x e (cons y e' w) =>
    by_cases hPx : P x
    · simp_all
    · by_cases hxu : u = x
      · simp_all
      · obtain ⟨v, hv, hv2⟩ := h
        rw [cons_vx, mem_cons] at hv
        obtain rfl | hvmem := hv
        · simp_all
        · have hexists : ∃ u ∈ (cons y e' w).vx, P u := by use v
          by_cases hnonempty : ((cons y e' w).endIf hexists).Nonempty
          · refine endIf_dropLast_mem_vx (w := cons y e' w) (by use v) hnonempty ?_
            by_cases hPy : P y
            · simp only [endIf_cons, hPx, ↓reduceDIte, hPy, dropLast_cons_nil, nil_vx, mem_cons,
                hxu, not_mem_nil, or_self] at hu
            · simpa [hPx, hPy, hxu] using hu
          · simp only [Nonempty.not_iff] at hnonempty
            obtain ⟨a, ha⟩ := hnonempty
            simp_all

lemma endIf_exists_inc₂_last {w : Walk α β} (h : ∃ u ∈ w.vx, P u) (hVd : w.ValidOn G)
    (hNonempty : (w.endIf h).Nonempty) : ∃ v ∈ (w.endIf h).vx, ¬ P v ∧ ∃ e, G.Inc₂ e v (w.endIf h).finish := by
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
        obtain ⟨a, ha, hh⟩ := endIf_exists_inc₂_last (w := w') h' hVd.2 hNonempty'
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
def Path (α β : Type*) := {w : Walk α β // w.vx.Nodup}

variable {p q : Path α β} {w1 w2 : Walk α β}
namespace Path

@[simp]
abbrev ofWalk [DecidableEq α] (w : Walk α β) : Path α β := ⟨w.dedup, w.dedup_vx_nodup⟩

-- /-- A path is valid on a graph if its underlying walk is valid -/
-- @[simp]
-- abbrev ValidOn (p : Path α β) (G : Graph α β) : Prop := p.val.ValidOn G

-- @[simp]
-- abbrev start (p : Path α β) : α := p.val.start

-- @[simp]
-- abbrev finish (p : Path α β) : α := p.val.finish

-- /-- List of vertices in a path -/
-- @[simp]
-- abbrev vx (p : Path α β) : List α := p.val.vx

-- /-- List of edges in a path -/
-- @[simp]
-- abbrev edge (p : Path α β) : List β := p.val.edge

-- /-- Length of a path -/
-- @[simp]
-- abbrev length (p : Path α β) : ℕ := p.val.length

/-- Create a nil path -/
@[simp]
def nil (x : α) : Path α β := ⟨Walk.nil x, by simp⟩

lemma nil_injective : Injective (nil : α → Path α β) := by
  rintro x y h
  rwa [nil, nil, ← Subtype.val_inj, nil.injEq] at h

@[simp]
lemma nil_inj : (nil x : Path α β) = nil y ↔ x = y := by
  rw [nil, nil, ← Subtype.val_inj, nil.injEq]

end Path

/-- Create a path from a single edge between two vertices -/
def Inc₂.path (hbtw : G.Inc₂ e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.walk, by simp [hne]⟩

namespace Path
/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {p : Path α β} (h : p.val.ValidOn G) (hle : G ≤ H) : p.val.ValidOn H :=
  Walk.ValidOn.le h hle

lemma of_cons {p : Path α β} (h : p.val = Walk.cons x e w) : w.vx.Nodup := by
  have := h ▸ p.prop
  rw [cons_vx, nodup_cons] at this
  exact this.2

lemma of_prefix {p : Path α β} (h : p.val = w1.append w2)
    (heq : w1.finish = w2.start) : w1.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ _ := append_vx' heq
  rw [← h] at this
  have : w1.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_left w1.vx w2.vx.tail
  exact this.nodup p.prop

lemma of_suffix {p : Path α β} (h : p.val = w1.append w2) : w2.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ w2.vx := append_vx
  rw [← h] at this
  have : w2.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_right w1.vx.dropLast w2.vx
  exact this.nodup p.prop

lemma not_mem_prefix_of_mem_suffix_tail {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem : u ∈ w2.vx.tail) : u ∉ w1.vx := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  exact (this.2.2 · hmem)

lemma not_mem_suffix_of_mem_prefix_dropLast {p : Path α β} (h : p.val = w1 ++ w2)
    (hmem : u ∈ w1.vx.dropLast) : u ∉ w2.vx := by
  have := h ▸ p.prop
  rw [append_vx, nodup_append] at this
  exact this.2.2 hmem

lemma eq_start_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w2.start := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  have := this.2.2 hmem1
  rw [← w2.vx.head_cons_tail vx_ne_nil, mem_cons, ← start_eq_vx_head] at hmem2
  simp_all only [imp_false, or_false]

lemma eq_finish_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w1.finish := heq ▸ eq_start_of_mem_prefix_suffix h heq hmem1 hmem2

def append (p q : Path α β) (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : Path α β :=
  ⟨p.val ++ q.val, by
    rw [append_vx]
    refine List.Nodup.append ?_ q.prop hDisj
    exact p.prop.sublist (List.dropLast_sublist p.val.vx)⟩

@[simp]
lemma append_start {p q : Path α β} (heq : p.val.finish = q.val.start)
    (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : (p.append q hDisj).val.start = p.val.start :=
  append_start_of_eq heq

@[simp]
lemma append_finish {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.finish = q.val.finish := by
  simp only [append, Walk.append_finish]

@[simp]
lemma append_length {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.length = p.val.length + q.val.length := by
  simp only [append, Walk.append_length]

@[simp]
lemma append_vx {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.vx = p.val.vx.dropLast ++ q.val.vx := by
  simp only [append, Walk.append_vx]

@[simp]
lemma append_edge {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.edge = p.val.edge ++ q.val.edge := by
  simp only [append, Walk.append_edge]

@[simp]
lemma append_validOn {p q : Path α β} (heq : p.val.finish = q.val.start)
    (hpVd : p.val.ValidOn G) (hqVd : q.val.ValidOn G)
    (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : (p.append q hDisj).val.ValidOn G :=
  Walk.append_validOn heq hpVd hqVd



lemma edge_not_isLoop {p : Path α β} (he : e ∈ p.val.edge) (hVd : p.val.ValidOn G) : ¬ G.IsLoopAt e x := by
  intro hloop
  rw [IsLoopAt_iff_inc₂] at hloop
  obtain ⟨w₁, w₂, hw12, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.Inc₂ e w₁.finish w₂.start := by
    simp only [ValidOn, hw12] at hVd
    obtain ⟨hbtw, H2⟩ := hVd.append_right_validOn
    exact hbtw
  have hNodup := hw12 ▸ p.prop
  simp only [Walk.append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hloop.eq_or_eq_of_inc₂ hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

lemma ne_of_inc₂_edge_mem (hVd : p.val.ValidOn G) (hbtw : G.Inc₂ e u v)
    (he : e ∈ p.val.edge) : u ≠ v := by
  rintro huv
  refine edge_not_isLoop (x := v) he hVd ?_
  rw [IsLoopAt_iff_inc₂]
  exact huv ▸ hbtw

@[simp]
lemma start_not_mem_vx_tail {p : Path α β} : p.val.start ∉ p.val.vx.tail := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.head_cons_tail vx_ne_nil, List.nodup_cons] at this
  exact this.1 (start_eq_vx_head ▸ hmem)

@[simp]
lemma finish_not_mem_vx_dropLast {p : Path α β} : p.val.finish ∉ p.val.vx.dropLast := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.dropLast_append_getLast vx_ne_nil, ← List.concat_eq_append,
    List.nodup_concat] at this
  exact this.2 (finish_eq_vx_getLast ▸ hmem)

@[simp]
lemma start_eq_finish_iff : p.val.start = p.val.finish ↔ ¬ p.val.Nonempty := by
  obtain ⟨w, hw⟩ := p
  simp only [start_eq_finish_iff hw, Nonempty.not_iff]

@[simp]
lemma start_ne_finish_iff : p.val.start ≠ p.val.finish ↔ p.val.Nonempty :=
  start_eq_finish_iff.not_left

end Path

@[simp]
lemma Inc₂.path_start (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.start = u := by simp only [path, Walk.start]

@[simp]
lemma Inc₂.path_finish (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.finish = v := by simp only [path, Walk.finish]

@[simp]
lemma Inc₂.path_length (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.length = 1 := by simp only [path, Walk.length]

@[simp]
lemma Inc₂.path_vx (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.vx = [u, v] := by simp only [path, Walk.vx]

@[simp]
lemma Inc₂.path_edge (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.edge = [e] := by simp only [path, Walk.edge]

@[simp]
lemma Inc₂.path_validOn (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.ValidOn G := walk_validOn hbtw

@[simp]
lemma Inc₂.path_validOn' (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.ValidOn (G[{u, v}]) := by
  refine (path_validOn hbtw hne).induce ?_
  rintro x hx
  simpa only [Set.mem_insert_iff, mem_singleton_iff, path_vx, mem_cons, not_mem_nil, or_false] using
    hx

lemma Connected.iff_path :
  G.Connected u v ↔ ∃ p : Path α β, p.val.ValidOn G ∧ p.val.start = u ∧ p.val.finish = v := by
  classical
  rw [Connected.iff_walk]
  constructor
  · rintro ⟨w, hwVd, rfl, rfl⟩
    use Path.ofWalk w, dedup_validOn hwVd, dedup_start w, dedup_finish w
  · rintro ⟨p, hpVd, rfl, rfl⟩
    use p.val, hpVd, rfl

lemma Contract.path {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidOn G p C)
    (h : w.ValidOn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.start → p y = w.finish →
    ∃ p' : Path α β, p'.val.ValidOn G ∧ p'.val.start = x ∧ p'.val.finish = y ∧
    {e | e ∈ p'.val.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  classical
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use Path.ofWalk w', dedup_validOn hw'Vd, dedup_start w', dedup_finish w',
    Subset.trans (dedup_edge_sublist w') hsub

section IsVxSetSeparator
namespace IsVxSetSeparator
variable {U V S T : Set α}

lemma path_inter {p : Path α β} (hUsep : G.IsVxSetSeparator U S T) (hVd : p.val.ValidOn G)
    (hS : p.val.start ∈ S) (hT : p.val.finish ∈ T) : ∃ x ∈ p.val.vx, x ∈ U := by
  by_contra! hx
  have hVdU : p.val.ValidOn (G - U) := by
    refine ValidOn.induce hVd ?_
    rintro x hxp
    exact ⟨hVd.mem_of_mem_vx hxp, hx x hxp⟩
  exact hUsep p.val.start hS p.val.finish hT <| Walk.connected_of_validOn hVdU

lemma walk_validOn_left (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G - U))
    (hLeft : ∃ x ∈ w.vx, x ∈ hUsep.leftSet) : w.ValidOn (G[hUsep.leftSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hLeft
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

lemma walk_validOn_right (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G - U))
    (hT : ∃ x ∈ w.vx, x ∈ hUsep.rightSet) :
    w.ValidOn (G[hUsep.rightSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hT
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

lemma path_in_leftHalf_of_finishSep {w : Walk α β} (hNodup : w.vx.Nodup) (hVd : w.ValidOn G)
    (hUsep : G.IsVxSetSeparator {w.finish} S T) (hS : w.start ∈ hUsep.leftSet) (hx : x ∈ w.vx) :
    x ∈ hUsep.leftSet ∪ {w.finish} := by
  obtain (h | h) := em (w.Nonempty) |>.symm
  · right
    rw [Nonempty.not_iff] at h
    obtain ⟨y, hy⟩ := h
    simpa only [hy, nil_finish, mem_singleton_iff, nil_vx, mem_cons, not_mem_nil, or_false] using hx
  rw [Nonempty.iff_exists_cons] at h
  obtain ⟨y, e, w', rfl⟩ := h
  simp only [cons_vx, mem_cons] at hx
  obtain (rfl | hx) := hx
  · left
    simpa only [cons_finish, cons_start] using hS
  · unfold leftSet
    simp only [cons_finish] at hUsep ⊢
    change x ∈ hUsep.leftSet ∪ {w'.finish}
    by_cases hw' : w'.start = w'.finish
    · simp [cons_vx_nodup hNodup] at hw'
      obtain ⟨y, rfl⟩ := hw'
      right
      simpa using hx
    · apply (path_in_leftHalf_of_finishSep (w := w') (cons_vx_nodup hNodup) hVd.of_cons hUsep · hx)
      simp only [cons_finish, cons_start] at hS
      obtain ⟨s, hs, hys⟩ := hS
      use s, hs, Connected.trans ?_ hys
      refine (hVd.1.induce_of_mem hys.mem_left ?_).connected.symm
      refine ⟨hVd.2.mem_of_mem_vx start_vx_mem, hw'⟩

lemma path_validOn_leftHalf_of_finishSep (hUsep : G.IsVxSetSeparator {p.val.finish} S T)
    (hVd : p.val.ValidOn G) (hS : p.val.start ∈ hUsep.leftSet) :
    p.val.ValidOn (G[hUsep.leftSet ∪ {p.val.finish}]) :=
  hVd.induce <| fun _ => path_in_leftHalf_of_finishSep (w := p.val) p.prop hVd hUsep hS

instance IsPreorder : IsPreorder (Set α) (IsVxSetSeparator G · S ·) where
  refl A s hs a ha hconn := by
    have := hconn.mem_right
    simp only [vxDel_V, mem_diff, ha, not_true_eq_false, and_false] at this
  trans A B C hAB hBC s hs c hc hconn := by
    rw [Connected.iff_path] at hconn
    obtain ⟨p, hpVd, rfl, rfl⟩ := hconn
    obtain ⟨x, hxp, hxB⟩ := hBC.path_inter (hpVd.le (induce_le G Set.diff_subset)) hs hc
    exact hAB p.val.start hs x hxB <| p.val.connected_of_validOn_of_mem hpVd start_vx_mem hxp

lemma crossingWalk_intersect (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.leftSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) : ∃ x ∈ w.vx, x ∈ V := by
  rw [mem_union] at hwstart hwfinish
  obtain (hV | ⟨s, hs, hconnStart⟩) := hwstart.symm <;> clear hwstart
  · use w.start, start_vx_mem
  obtain (hV | ⟨t, ht, hconnFinish⟩) := hwfinish.symm <;> clear hwfinish
  · use w.finish, finish_vx_mem
  by_contra! hw
  have hVd : w.ValidOn (G - V) :=
    hwVd.induce fun x hx ↦ ⟨hwVd.mem_of_mem_vx hx, hw x hx⟩
  exact hVsep s hs t ht <| hconnStart.symm.trans (w.connected_of_validOn hVd) |>.trans hconnFinish

lemma crossingWalk_intersect' (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.rightSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.leftSet ∪ V) : ∃ x ∈ w.vx, x ∈ V :=
  crossingWalk_intersect hVsep.symm hwVd hwstart hwfinish

lemma crossingWalk_endIf_validOn [DecidableEq α] (hVsep : G.IsVxSetSeparator V S T)
    [DecidablePred (· ∈ V)] {w : Walk α β} (hwVd : w.ValidOn G)
    (hwstart : w.start ∈ hVsep.leftSet ∪ V) (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) :
    (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect hwVd hwstart hwfinish)).ValidOn (G[hVsep.leftSet ∪ V]) := by
  let h := hVsep.crossingWalk_intersect hwVd hwstart hwfinish
  refine endIf_validOn h hwVd |>.induce ?_
  rintro x hx
  by_cases hnonempty : ¬ (w.endIf h).Nonempty
  · rw [Nonempty.not_iff] at hnonempty
    obtain ⟨y, hy⟩ := hnonempty
    simp only [hy, nil_vx, mem_cons, not_mem_nil, or_false] at hx
    subst y
    right
    convert endIf_finish h
    simp only [hy, nil_finish]
  rw [not_not] at hnonempty
  obtain (rfl | hxV) := mem_dropLast_or_finish_of_mem hx |>.symm
  · right
    exact endIf_finish h
  · have := dropLast_validOn (endIf_validOn h hwVd)
    have : Walk.ValidOn _ (G - V):= this.induce fun x hx ↦
      ⟨this.mem_of_mem_vx hx, endIf_dropLast_mem_vx h hnonempty hx⟩
    simp only [endIf_nonempty_iff] at hnonempty
    simp only [mem_union, hnonempty, or_false] at hwstart
    left
    refine (hVsep.walk_validOn_left this ?_).mem_of_mem_vx hxV
    use w.start, ?_
    convert start_vx_mem using 1
    simp only [endIf_nonempty_iff, hnonempty, not_false_eq_true, dropLast_start, endIf_start]

lemma crossingWalk_endIf_validOn' [DecidableEq α] [DecidablePred (· ∈ V)]
    (hVsep : G.IsVxSetSeparator V S T)
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.rightSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.leftSet ∪ V) : (w.endIf (P := (· ∈ V))
    (hVsep.crossingWalk_intersect' hwVd hwstart hwfinish)).ValidOn (G[hVsep.rightSet ∪ V]) :=
  hVsep.symm.crossingWalk_endIf_validOn hwVd hwstart hwfinish

lemma leftSetV_iff (h : G.IsVxSetSeparator V S T) (hV : V ⊆ G.V) (U : Set α) :
    G[h.leftSet ∪ V].IsVxSetSeparator U S V ↔ G.IsVxSetSeparator U S V := by
  classical
  constructor
  · rintro hUsep s hs v hv hconn
    rw [Connected.iff_walk] at hconn
    obtain ⟨w, hwVd, rfl, rfl⟩ := hconn
    have hwVdG : w.ValidOn G := hwVd.le (induce_le _ Set.diff_subset)
    have hwstart : w.start ∈ h.leftSet ∪ V := by
      by_cases hsUv : w.start ∈ V
      · right
        exact hsUv
      · left
        use w.start, hs
        refine Connected.refl ⟨?_, hsUv⟩
        exact Set.diff_subset <| hwVd.mem_of_mem_vx (Walk.start_vx_mem)
    have hwfinish : w.finish ∈ h.rightSet ∪ V := Set.mem_union_right h.rightSet hv
    have hw' : ∃ x ∈ w.vx, x ∈ V := h.crossingWalk_intersect hwVdG hwstart hwfinish
    have := h.crossingWalk_endIf_validOn hwVdG hwstart hwfinish
    let w' := w.endIf (P := (· ∈ V)) hw'
    apply hUsep w'.start (by rwa [Walk.endIf_start]) w'.finish (Walk.endIf_finish hw')
    rw [← vxDel_notation, induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V]
    apply w'.connected_of_validOn
    apply (Walk.endIf_validOn hw' hwVdG).induce
    rintro x hx
    exact ⟨this.mem_of_mem_vx hx, (hwVd.mem_of_mem_vx (Walk.endIf_vx_sublist hw' hx)).2⟩
    · exact Set.diff_subset
  · rintro hUsep
    refine hUsep.le <| induce_le _ <| Set.union_subset ?_ hV
    exact (leftSet_subset h).trans diff_subset

lemma rightSetV_iff (hVsep : G.IsVxSetSeparator V S T) (hV : V ⊆ G.V) (U : Set α) :
    G[hVsep.rightSet ∪ V].IsVxSetSeparator U V T ↔ G.IsVxSetSeparator U V T := by
  have := hVsep.symm.leftSetV_iff hV U
  rw [comm (S := V), comm (S := V)]
  convert this using 1

lemma conn_sep_iff_conn_left (hVsep : G.IsVxSetSeparator V S T) (hu : u ∈ hVsep.leftSet)
    (hV : V ⊆ G.V) :
    (∃ v ∈ V, G.Connected u v) ↔ ∃ v ∈ V, G[hVsep.leftSet ∪ V].Connected u v := by
  classical
  constructor
  · rintro ⟨v, hv, hconn⟩
    rw [Connected.iff_walk] at hconn
    obtain ⟨w, hwVd, rfl, rfl⟩ := hconn
    have hw' : ∃ u ∈ w.vx, (fun x ↦ x ∈ V) u := by use w.finish, finish_vx_mem
    let w' := w.endIf (P := (· ∈ V)) hw'
    use w'.finish, Walk.endIf_finish hw'
    rw [Connected.iff_walk]
    use w', ?_, endIf_start hw'
    have hw'VdG : w'.ValidOn G := endIf_validOn hw' hwVd
    refine hw'VdG.induce ?_
    rintro x hxw'
    by_cases hNonempty : w'.Nonempty
    · by_cases hxw'Finish : x = w'.finish
      · subst x
        right
        exact endIf_finish hw'
      · have hw'dVdG : w'.dropLast.ValidOn G := dropLast_validOn hw'VdG
        have hw'dvdGV : w'.dropLast.ValidOn (G - V) := by
          refine ValidOn.induce hw'dVdG ?_
          rintro z hz
          exact ⟨hw'dVdG.mem_of_mem_vx hz, endIf_dropLast_mem_vx hw' hNonempty hz⟩
        have : w'.dropLast.ValidOn (G[hVsep.leftSet]) := by
          refine ValidOn.induce hw'dVdG ?_
          rintro y hy
          simp only [leftSet, mem_setOf_eq]
          obtain ⟨s, hs, hsconn⟩ := hu
          use s, hs
          rw [← endIf_start hw', ← dropLast_start hNonempty] at hsconn
          refine Connected.trans ?_ hsconn
          exact w'.dropLast.connected_of_validOn_of_mem hw'dvdGV hy start_vx_mem

        rw [← List.dropLast_concat_getLast vx_ne_nil, List.mem_append, ← dropLast_vx hNonempty,
        List.mem_singleton, ← w'.finish_eq_vx_getLast] at hxw'
        simp only [hxw'Finish, or_false] at hxw'
        left
        exact this.mem_of_mem_vx hxw'
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, hy⟩ := hNonempty
      simp only [hy, nil_vx, mem_cons, not_mem_nil, or_false] at hxw'
      subst y
      right
      have : w'.finish = x := by
        simp only [hy, nil_finish]
      exact this ▸ endIf_finish hw'
  · rintro ⟨v, hv, hconn⟩
    use v, hv
    refine hconn.le (induce_le G ?_)
    exact union_subset (hVsep.leftSet_subset.trans diff_subset) hV

end IsVxSetSeparator
end IsVxSetSeparator


-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

namespace Path
section disjoint

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.val.vx → x ∈ pj.val.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.val.vx → x ∈ pj.val.vx → pi = pj

end disjoint

end Path
