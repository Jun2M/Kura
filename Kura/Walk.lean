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

def dropLast : Walk α β → Walk α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

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

@[simp] lemma nil_injective : Injective (nil : α → Walk α β) := by
  rintro x y h
  rwa [nil.injEq] at h

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

lemma ValidOn.append_left_validOn (h : w₁.finish = w₂.start) (hw₁ : w₁.Nonempty)
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
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_start, cons_start]
  | .cons x e (cons y e' w) => simp only [dropLast, cons_start]

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
    · simp only [cons_finish, dropLast_cons_cons, mem_iff, cons_vx, Nonempty.cons_true,
      dropLast_vx, mem_cons, true_or, or_true]
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
    ∃ w₁ w₂ : Walk α β, w = w₁.append w₂ ∧ w₁.finish = u ∧ w₂.start = u := by
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

variable [DecidableEq α] {p : Path α β}
namespace Path

@[simp]
abbrev ofWalk (w : Walk α β) : Path α β := ⟨w.dedup, w.dedup_vx_nodup⟩

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
def IsBetween.path (hbtw : G.IsBetween e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.walk, by simp [hne]⟩

namespace Path
/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {p : Path α β} (h : p.val.ValidOn G) (hle : G ≤ H) : p.val.ValidOn H :=
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

lemma not_mem_prefix_of_mem_suffix_tail {p : Path α β} {w1 w2 : Walk α β}
    (h : p.val = w1.append w2) (heq : w1.finish = w2.start) (hmem : u ∈ w2.vx.tail) : u ∉ w1.vx := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  exact (this.2.2 · hmem)

lemma not_mem_suffix_of_mem_prefix_dropLast {p : Path α β} {w1 w2 : Walk α β}
    (h : p.val = w1.append w2) (hmem : u ∈ w1.vx.dropLast) : u ∉ w2.vx := by
  have := h ▸ p.prop
  rw [append_vx, nodup_append] at this
  exact this.2.2 hmem

lemma eq_start_of_mem_prefix_suffix {p : Path α β} {w1 w2 : Walk α β}
    (h : p.val = w1.append w2) (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w2.start := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  have := this.2.2 hmem1
  rw [← w2.vx.head_cons_tail vx_ne_nil, mem_cons, ← start_eq_vx_head] at hmem2
  simp_all only [imp_false, or_false]

lemma eq_finish_of_mem_prefix_suffix {p : Path α β} {w1 w2 : Walk α β}
    (h : p.val = w1.append w2) (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w1.finish := heq ▸ eq_start_of_mem_prefix_suffix h heq hmem1 hmem2

def append (p q : Path α β) (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : Path α β :=
  ⟨p.val.append q.val, by
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

lemma edge_not_isLoop (he : e ∈ p.val.edge) (hVd : p.val.ValidOn G) : ¬ G.IsLoop e := by
  intro hloop
  rw [IsLoop_iff_IsBetween] at hloop
  obtain ⟨x, hbtw⟩ := hloop
  obtain ⟨w₁, w₂, hw12, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.IsBetween e w₁.finish w₂.start := by
    simp only [ValidOn, hw12] at hVd
    obtain ⟨hbtw, H2⟩ := hVd.append_right_validOn
    exact hbtw
  have hNodup := hw12 ▸ p.prop
  simp only [Walk.append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hbtw.eq_or_eq_of_IsBetween hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

lemma ne_of_isBetween_edge_mem (hVd : p.val.ValidOn G) (hbtw : G.IsBetween e u v)
    (he : e ∈ p.val.edge) : u ≠ v := by
  rintro huv
  refine edge_not_isLoop he hVd ?_
  rw [IsLoop_iff_IsBetween]
  exact ⟨v, huv ▸ hbtw⟩

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

end Path

@[simp]
lemma IsBetween.path_start (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.start = u := by simp only [path, Walk.start]

@[simp]
lemma IsBetween.path_finish (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.finish = v := by simp only [path, Walk.finish]

@[simp]
lemma IsBetween.path_length (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.length = 1 := by simp only [path, Walk.length]

@[simp]
lemma IsBetween.path_vx (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.vx = [u, v] := by simp only [path, Walk.vx]

@[simp]
lemma IsBetween.path_edge (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.edge = [e] := by simp only [path, Walk.edge]

@[simp]
lemma IsBetween.path_validOn (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.ValidOn G := walk_validOn hbtw

@[simp]
lemma IsBetween.path_validOn' (hbtw : G.IsBetween e u v) (hne : u ≠ v) :
    (IsBetween.path hbtw hne).val.ValidOn (G[{u, v}]) := by
  refine (path_validOn hbtw hne).induce ?_
  rintro x hx
  simpa only [Set.mem_insert_iff, mem_singleton_iff, path_vx, mem_cons, not_mem_nil, or_false] using
    hx

lemma Connected.iff_path : G.Connected u v ↔ ∃ p : Path α β, p.val.ValidOn G ∧ p.val.start = u ∧
  p.val.finish = v := by
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
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use Path.ofWalk w', dedup_validOn hw'Vd, dedup_start w', dedup_finish w',
    Subset.trans (dedup_edge_sublist w') hsub

section IsVxSetSeparator
namespace IsVxSetSeparator
variable {U V S T : Set α}

lemma path_inter (hUsep : G.IsVxSetSeparator U S T) (hVd : p.val.ValidOn G)
    (hS : p.val.start ∈ S) (hT : p.val.finish ∈ T) : ∃ x ∈ p.val.vx, x ∈ U := by
  by_contra! hx
  have hVdU : p.val.ValidOn (G[G.V \ U]) := by
    refine ValidOn.induce hVd ?_
    rintro x hxp
    exact ⟨hVd.mem_of_mem_vx hxp, hx x hxp⟩
  exact hUsep p.val.start hS p.val.finish hT <| Walk.connected_of_validOn hVdU

omit [DecidableEq α] in
lemma walk_validOn_left (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G[G.V \ U]))
    (hS : ∃ x ∈ w.vx, x ∈ hUsep.leftSet) :
    w.ValidOn (G[hUsep.leftSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hS
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

omit [DecidableEq α] in
lemma walk_validOn_right (hUsep : G.IsVxSetSeparator U S T) (hVd : w.ValidOn (G[G.V \ U]))
    (hT : ∃ x ∈ w.vx, x ∈ hUsep.rightSet) :
    w.ValidOn (G[hUsep.rightSet]) := by
  obtain ⟨y, hy, s, hs, hys⟩ := hT
  refine hVd.le (induce_le G diff_subset) |>.induce fun x hxp ↦ ?_
  use s, hs, (w.connected_of_validOn_of_mem hVd hxp hy).trans hys

instance IsPreorder : IsPreorder (Set α) (IsVxSetSeparator G · S ·) where
  refl A s hs a ha hconn := by
    have := hconn.mem_right
    simp only [induce_V, mem_diff, ha, not_true_eq_false, and_false] at this
  trans A B C hAB hBC s hs c hc hconn := by
    rw [Connected.iff_path] at hconn
    obtain ⟨p, hpVd, rfl, rfl⟩ := hconn
    obtain ⟨x, hxp, hxB⟩ := hBC.path_inter (hpVd.le (induce_le G Set.diff_subset)) hs hc
    exact hAB p.val.start hs x hxB <| p.val.connected_of_validOn_of_mem hpVd start_vx_mem hxp

omit [DecidableEq α] in
lemma crossingWalk_intersect (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.leftSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) : ∃ x ∈ w.vx, x ∈ V := by
  rw [mem_union] at hwstart hwfinish
  obtain (hV | ⟨s, hs, hconnStart⟩) := hwstart.symm <;> clear hwstart
  · use w.start, start_vx_mem
  obtain (hV | ⟨t, ht, hconnFinish⟩) := hwfinish.symm <;> clear hwfinish
  · use w.finish, finish_vx_mem
  by_contra! hw
  have hVd : w.ValidOn (G[G.V \ V]) :=
    hwVd.induce fun x hx ↦ ⟨hwVd.mem_of_mem_vx hx, hw x hx⟩
  exact hVsep s hs t ht <| hconnStart.symm.trans (w.connected_of_validOn hVd) |>.trans hconnFinish

omit [DecidableEq α] in
lemma crossingWalk_intersect' (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.rightSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.leftSet ∪ V) : ∃ x ∈ w.vx, x ∈ V :=
  crossingWalk_intersect hVsep.symm hwVd hwstart hwfinish

lemma crossingWalk_endIf_validOn (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
    {w : Walk α β} (hwVd : w.ValidOn G) (hwstart : w.start ∈ hVsep.leftSet ∪ V)
    (hwfinish : w.finish ∈ hVsep.rightSet ∪ V) : (w.endIf (P := (· ∈ V))
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
    have : Walk.ValidOn _ (G[G.V \ V]):= this.induce fun x hx ↦
      ⟨this.mem_of_mem_vx hx, endIf_dropLast_mem_vx h hnonempty hx⟩
    simp only [endIf_nonempty_iff] at hnonempty
    simp only [mem_union, hnonempty, or_false] at hwstart
    left
    refine (hVsep.walk_validOn_left this ?_).mem_of_mem_vx hxV
    use w.start, ?_
    convert start_vx_mem using 1
    simp only [endIf_nonempty_iff, hnonempty, not_false_eq_true, dropLast_start, endIf_start]

lemma crossingWalk_endIf_validOn' (hVsep : G.IsVxSetSeparator V S T) [DecidablePred (· ∈ V)]
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
    rw [induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V]
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
        have hw'dvdGV : w'.dropLast.ValidOn (G[G.V \ V]) := by
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

structure PathEnsemble (α β : Type*) [DecidableEq α] where
  Paths : Set (Path α β)
  Disj : Disjoint Paths

namespace PathEnsemble

def Empty (α β : Type*) [DecidableEq α] : PathEnsemble α β where
  Paths := ∅
  Disj := by
    rintro x p q hp hq hxp hxq
    exact False.elim hp

def nil (U : Set α) (β : Type*) : PathEnsemble α β where
  Paths := Path.nil '' U
  Disj := by
    rintro x p q hp hq hxp hxq
    simp only [mem_image] at hp hq
    obtain ⟨u, hu, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hq
    simp only [vx, Graph.Path.nil, nil_vx, mem_cons, not_mem_nil, or_false] at hxp hxq
    subst u v
    rfl

def ValidOn (Ps : PathEnsemble α β) (G : Graph α β) := ∀ p ∈ Ps.Paths, p.val.ValidOn G

def StartSet (Ps : PathEnsemble α β) : Set α := (·.val.start) '' Ps.Paths

def FinishSet (Ps : PathEnsemble α β) : Set α := (·.val.finish) '' Ps.Paths

def VxSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.val.vx}

def EdgeSet (Ps : PathEnsemble α β) : Set β := {e | ∃ p ∈ Ps.Paths, e ∈ p.val.edge}

def InternalVsSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.val.vx.tail.dropLast}

def insert (p : Path α β) (Ps : PathEnsemble α β) (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) : PathEnsemble α β where
  Paths := Ps.Paths ∪ {p}
  Disj := by
    rintro x p₁ p₂ hp1 hp2 hxp hxq
    simp only [union_singleton, Set.mem_insert_iff] at hp1 hp2
    simp only [VxSet, mem_setOf_eq, not_exists, not_and] at h
    obtain (rfl | h1) := hp1 <;> obtain (rfl | h2) := hp2
    · rfl
    · exact (h x hxp p₂ h2 hxq).elim
    · exact (h x hxq p₁ h1 hxp).elim
    · exact Ps.Disj x p₁ p₂ h1 h2 hxp hxq

lemma start_injOn (Ps : PathEnsemble α β) : InjOn (·.val.start) Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hstart
  exact Ps.Disj _ _ _ hp₁ hp₂ start_vx_mem (by
    beta_reduce at hstart
    exact hstart ▸ start_vx_mem)

lemma finish_injOn (Ps : PathEnsemble α β) : InjOn (·.val.finish) Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hfinish
  exact Ps.Disj _ _ _ hp₁ hp₂ finish_vx_mem (by
    beta_reduce at hfinish
    exact hfinish ▸ finish_vx_mem)

lemma unique_path_start (Ps : PathEnsemble α β)  :
    ∀ x ∈ Ps.StartSet, ∃! p ∈ Ps.Paths, p.val.start = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ start_injOn Ps hq.1 hp hq.2)

lemma unique_path_finish (Ps : PathEnsemble α β) :
    ∀ x ∈ Ps.FinishSet, ∃! p ∈ Ps.Paths, p.val.finish = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ finish_injOn Ps hq.1 hp hq.2)

noncomputable def byStart (Ps : PathEnsemble α β) (u : α) (hu : u ∈ Ps.StartSet) : Path α β :=
  (Ps.unique_path_start u hu).choose

noncomputable def byFinish (Ps : PathEnsemble α β) (u : α) (hu : u ∈ Ps.FinishSet) : Path α β :=
  (Ps.unique_path_finish u hu).choose

variable {Ps : PathEnsemble α β} {u : α}

@[simp]
lemma byStart_mem (hu : u ∈ Ps.StartSet) :
    Ps.byStart u hu ∈ Ps.Paths := (Ps.unique_path_start u hu).choose_spec.1.1

@[simp]
lemma byFinish_mem (hu : u ∈ Ps.FinishSet) :
    Ps.byFinish u hu ∈ Ps.Paths := (Ps.unique_path_finish u hu).choose_spec.1.1

@[simp]
lemma byStart_start (hu : u ∈ Ps.StartSet) :
    (Ps.byStart u hu).val.start = u := (Ps.unique_path_start u hu).choose_spec.1.2

@[simp]
lemma byFinish_finish (hu : u ∈ Ps.FinishSet) :
    (Ps.byFinish u hu).val.finish = u := (Ps.unique_path_finish u hu).choose_spec.1.2

lemma byStart_injective (Ps : PathEnsemble α β) :
    Injective (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byStart_start x.prop, h, byStart_start y.prop]

lemma byFinish_injective (Ps : PathEnsemble α β) :
    Injective (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byFinish_finish x.prop, h, byFinish_finish y.prop]

variable {Ps : PathEnsemble α β} {u v x y : α} {p q : Path α β} {U : Set α}

@[simp]
lemma byStart_inj (hu : u ∈ Ps.StartSet) (hv : v ∈ Ps.StartSet) :
    Ps.byStart u hu = Ps.byStart v hv ↔ u = v := by
  change (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) ⟨u, hu⟩ = (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) ⟨v, hv⟩ ↔ u = v
  rw [byStart_injective Ps |>.eq_iff, Subtype.ext_iff]

@[simp]
lemma byFinish_inj (hu : u ∈ Ps.FinishSet) (hv : v ∈ Ps.FinishSet) :
    Ps.byFinish u hu = Ps.byFinish v hv ↔ u = v := by
  change (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) ⟨u, hu⟩ = (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) ⟨v, hv⟩ ↔ u = v
  rw [byFinish_injective Ps |>.eq_iff, Subtype.ext_iff]

lemma mem_finishSet_mem (hu : u ∈ Ps.FinishSet) (hup : u ∈ p.val.vx) (hp : p ∈ Ps.Paths) :
    u = p.val.finish := by
  obtain ⟨q, hq, rfl⟩ := hu
  rw [Ps.Disj q.val.finish q p hq hp finish_vx_mem hup]

lemma mem_startSet_mem (hv : v ∈ Ps.StartSet) (hvp : v ∈ p.val.vx) (hp : p ∈ Ps.Paths) :
    v = p.val.start := by
  obtain ⟨q, hq, rfl⟩ := hv
  rw [Ps.Disj q.val.start q p hq hp start_vx_mem hvp]

@[simp]
lemma start_mem_StartSet (hp : p ∈ Ps.Paths) : p.val.start ∈ Ps.StartSet := by
  use p, hp

@[simp]
lemma finish_mem_FinishSet (hp : p ∈ Ps.Paths) : p.val.finish ∈ Ps.FinishSet := by
  use p, hp

@[simp]
lemma byStart_of_start (hp : p ∈ Ps.Paths) : Ps.byStart p.val.start (start_mem_StartSet hp) = p :=
  ((Ps.unique_path_start p.val.start (start_mem_StartSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

@[simp]
lemma byFinish_of_finish (hp : p ∈ Ps.Paths) : Ps.byFinish p.val.finish (finish_mem_FinishSet hp) = p :=
  ((Ps.unique_path_finish p.val.finish (finish_mem_FinishSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

lemma append_aux {Ps₁ Ps₂ : PathEnsemble α β} (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (hu : u ∈ Ps₁.FinishSet) (hv : v ∈ Ps₂.StartSet)
    (hx1 : x ∈ (Ps₁.byFinish u hu).val.vx.dropLast) (hx2 : x ∈ (Ps₂.byStart v hv).val.vx) :
    False := by
  have hx1' : x ∈ Ps₁.VxSet := by
    use Ps₁.byFinish u hu, byFinish_mem hu, List.mem_of_mem_dropLast hx1
  have hx2' : x ∈ Ps₂.VxSet := by
    use Ps₂.byStart v hv, byStart_mem hv, hx2
  have := mem_finishSet_mem (hsu ⟨hx1', hx2'⟩) (List.mem_of_mem_dropLast hx1) (byFinish_mem hu)
  exact finish_not_mem_vx_dropLast (this ▸ hx1)

def append (Ps₁ Ps₂ : PathEnsemble α β) (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : PathEnsemble α β where
  Paths :=
    let f : ↑(Ps₁.FinishSet) → Path α β := fun ⟨a, ha⟩ ↦
      Ps₁.byFinish a ha|>.append (Ps₂.byStart a (heq ▸ ha)) fun b ↦ append_aux hsu ha (heq ▸ ha)
    Set.range f
  Disj x p q hp hq hxp hxq := by
    simp only [Set.mem_range, Subtype.exists] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    simp only [append_vx, mem_append] at hxp hxq
    obtain (hxp1 | hxp2) := hxp <;> obtain (hxq1 | hxq2) := hxq
    · have := Ps₁.Disj x _ _ (byFinish_mem ha) (byFinish_mem hb) (List.dropLast_subset _ hxp1) (List.dropLast_subset _ hxq1)
      rw [byFinish_inj] at this
      subst b
      rfl
    · exact (append_aux hsu ha (heq ▸ hb) hxp1 hxq2).elim
    · exact (append_aux hsu hb (heq ▸ ha) hxq1 hxp2).elim
    · have := Ps₂.Disj x _ _ (byStart_mem (heq ▸ ha)) (byStart_mem (heq ▸ hb)) hxp2 hxq2
      rw [byStart_inj] at this
      subst b
      rfl

-- def appendOnSep (Ps₁ Ps₂ : PathEnsemble α β) (heq : Ps₁.FinishSet = Ps₂.StartSet)
--     (hsep : G.IsVxSetSeparator Ps₁.FinishSet Ps₁.StartSet Ps₂.FinishSet) : PathEnsemble α β :=
--   Ps₁.append Ps₂ (by
--     rintro x ⟨⟨p, hp1, hxp⟩, q, hq2, hxq⟩


--     rw [h1Finish] at hx
--     exact hsep.1 hx) (by
--     rintro x hx
--     rw [h2Start] at hx
--     exact hsep.2 hx)

@[simp]
lemma Empty_validOn : (Empty α β).ValidOn G := by
  rintro p hp
  exact False.elim hp

@[simp]
lemma Empty_finite : (Empty α β).Paths.Finite := by
  simp only [Empty, finite_empty]

@[simp]
lemma Empty_ncard : (Empty α β).Paths.ncard = 0 := by
  simp only [Empty, ncard_empty]

@[simp]
lemma Empty_VxSet : (Empty α β).VxSet = ∅ := by
  simp only [VxSet, Empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_EdgeSet : (Empty α β).EdgeSet = ∅ := by
  simp only [EdgeSet, Empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_startSet : (Empty α β).StartSet = ∅ := by
  simp only [StartSet, Empty, image_empty]

@[simp]
lemma Empty_finishSet : (Empty α β).FinishSet = ∅ := by
  simp only [FinishSet, Empty, image_empty]

@[simp]
lemma nil_validOn : (nil U β).ValidOn (G[U]) := by
  rintro p ⟨x, hx, rfl⟩
  simpa only [Path.nil, nil_validOn_iff, induce_V]

@[simp]
lemma nil_validOn' (hUV : U ⊆ G.V) : (nil U β).ValidOn G := by
  rintro p ⟨x, hx, rfl⟩
  simp only [Path.nil, nil_validOn_iff]
  exact hUV hx

@[simp]
lemma mem_nil_iff : p ∈ (nil U β).Paths ↔ ∃ u ∈ U, Path.nil u = p := by
  simp only [nil, mem_image]

@[simp]
lemma nil_VxSet : (nil U β).VxSet = U := by
  simp only [VxSet, mem_nil_iff, Path.nil, vx, exists_exists_and_eq_and, nil_vx, mem_cons,
    not_mem_nil, or_false, exists_eq_right', setOf_mem_eq]

@[simp]
lemma nil_startSet : (nil U β).StartSet = U := by
  simp only [StartSet, start, nil, Path.nil, image_image, nil_start, image_id']

@[simp]
lemma nil_finishSet : (nil U β).FinishSet = U := by
  simp only [FinishSet, finish, nil, Path.nil, image_image, nil_finish, image_id']

@[simp]
lemma nil_ncard : (nil U β).Paths.ncard = U.ncard :=
  ncard_image_of_injective U nil_injective

lemma startSet_subset_VxSet : Ps.StartSet ⊆ Ps.VxSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, start_vx_mem

lemma finishSet_subset_VxSet : Ps.FinishSet ⊆ Ps.VxSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, finish_vx_mem

lemma VxSet_subset_of_validOn (hVd : Ps.ValidOn G) : Ps.VxSet ⊆ G.V := by
  rintro x ⟨p, hp, hx⟩
  exact (hVd p hp).mem_of_mem_vx hx

lemma StartSet_ncard : Ps.StartSet.ncard = Ps.Paths.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.val.start)
  · rintro p hp
    use p
  · rintro p q hp hq hstart
    exact Ps.Disj p.val.start p q hp hq start_vx_mem (hstart ▸ start_vx_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma FinishSet_ncard : Ps.FinishSet.ncard = Ps.Paths.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.val.finish)
  · rintro p hp
    use p
  · rintro p q hp hq hfinish
    exact Ps.Disj p.val.finish p q hp hq finish_vx_mem (hfinish ▸ finish_vx_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma ValidOn.le {G' : Graph α β} (h : G ≤ G') (hVd : Ps.ValidOn G) :
    Ps.ValidOn G' := fun p hp ↦ (hVd p hp).le h

lemma finite_of_finite_graph (h : G.Finite) (hVd : Ps.ValidOn G) : Ps.Paths.Finite := by
  have hle := (Ps.startSet_subset_VxSet).trans (Ps.VxSet_subset_of_validOn hVd)
  have hst : Ps.StartSet.Finite := Finite.subset h.1 hle
  exact (finite_image_iff Ps.start_injOn).mp hst

@[simp]
lemma mem_insert_iff (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    q ∈ (Ps.insert p h).Paths ↔ q = p ∨ q ∈ Ps.Paths := by
  simp only [insert, union_singleton, Set.mem_insert_iff]

lemma insert_validOn (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) (hVd : Ps.ValidOn G)
    (hpVd : p.val.ValidOn G) : (Ps.insert p h).ValidOn G := by
  rintro q hq
  rw [mem_insert_iff] at hq
  obtain (rfl | hq) := hq
  · exact hpVd
  · exact hVd q hq

@[simp]
lemma insert_ncard (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) (hFin : Ps.Paths.Finite) :
    (Ps.insert p h).Paths.ncard = Ps.Paths.ncard + 1 := by
  simp only [VxSet, mem_setOf_eq, not_exists, not_and, insert, union_singleton] at h ⊢
  refine Set.ncard_insert_of_not_mem (fun hp ↦ ?_) hFin
  obtain ⟨a, as, has⟩ := List.ne_nil_iff_exists_cons.mp (vx_ne_nil (w := p.val))
  specialize h a (by simp only [has, mem_cons, true_or]) p hp
  simp only [has, mem_cons, true_or, not_true_eq_false] at h

@[simp]
lemma insert_startSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).StartSet = Ps.StartSet ∪ {p.val.start} := by
  simp only [StartSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_finishSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).FinishSet = Ps.FinishSet ∪ {p.val.finish} := by
  simp only [FinishSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_VxSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).VxSet = {u | u ∈ p.val.vx} ∪ Ps.VxSet := by
  ext x
  simp +contextual only [VxSet, insert, union_singleton, Set.mem_insert_iff, exists_eq_or_imp,
    mem_setOf_eq, mem_union]


variable {Ps₁ Ps₂ : PathEnsemble α β}

lemma append_validOn (hPs₁Vd : Ps₁.ValidOn G) (hPs₂Vd : Ps₂.ValidOn G)
    (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet) (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).ValidOn G := by
  rintro p ⟨⟨a, ha⟩, _, rfl⟩
  refine Walk.append_validOn ?_ (hPs₁Vd _ (byFinish_mem ha)) (hPs₂Vd _ (byStart_mem (heq ▸ ha)))
  simp only [byFinish_finish, byStart_start]

@[simp]
lemma append_startSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : (Ps₁.append Ps₂ hsu heq).StartSet = Ps₁.StartSet := by
  ext x
  simp +contextual only [StartSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  constructor
  · rintro p u hu ⟨_, rfl⟩ rfl
    use Ps₁.byFinish u hu, byFinish_mem _, by simp only [byFinish_finish, byStart_start, append_start]
  · rintro p hp1 rfl
    use (Ps₁.byFinish p.val.finish (heq ▸ finish_mem_FinishSet hp1)).append
      (Ps₂.byStart p.val.finish <| heq ▸ finish_mem_FinishSet hp1) fun b ↦
      append_aux hsu (finish_mem_FinishSet hp1) (heq ▸ finish_mem_FinishSet hp1)
    use ?_, by simp only [hp1, byFinish_of_finish, byStart_start, append_start]
    use p.val.finish, finish_mem_FinishSet hp1

@[simp]
lemma append_finishSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : (Ps₁.append Ps₂ hsu heq).FinishSet = Ps₂.FinishSet := by
  ext x
  simp +contextual only [FinishSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  refine ⟨?_, ?_⟩
  · rintro p u q ⟨hq, rfl⟩ rfl rfl
    exact ⟨Ps₂.byStart q.val.finish (heq ▸ finish_mem_FinishSet hq), byStart_mem _, by rw [append_finish]⟩
  · rintro p hp rfl
    use (Ps₁.byFinish p.val.start (heq ▸ start_mem_StartSet hp)).append
      (Ps₂.byStart p.val.start <| heq ▸ start_mem_StartSet hp) fun b ↦
      append_aux hsu (heq ▸ start_mem_StartSet hp) (heq ▸ start_mem_StartSet hp)
    use ?_, by simp only [hp, byStart_of_start, append_finish]
    use p.val.start, ?_
    use Ps₁.byFinish p.val.start (heq ▸ start_mem_StartSet hp), byFinish_mem _, by simp only [byFinish_finish]

@[simp]
lemma append_ncard_eq_left (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₁.Paths.ncard := by
  rw [← StartSet_ncard, append_startSet hsu heq, ← StartSet_ncard]

@[simp]
lemma append_ncard_eq_right (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₂.Paths.ncard := by
  rw [← FinishSet_ncard, append_finishSet hsu heq, ← FinishSet_ncard]

lemma append_VxSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
  (Ps₁.append Ps₂ hsu heq).VxSet = Ps₁.VxSet ∪ Ps₂.VxSet := by
  ext x
  simp +contextual only [VxSet, append, Set.mem_range, Subtype.exists, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨p, ⟨u, hu, rfl⟩, hx⟩
    simp only [append_vx, mem_append] at hx
    refine hx.imp ?_ ?_
    · rintro h
      use Ps₁.byFinish u hu, byFinish_mem _, List.mem_of_mem_dropLast h
    · rintro h
      use Ps₂.byStart u (heq ▸ hu), byStart_mem _, h
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · use (Ps₁.byFinish p.val.finish <| finish_mem_FinishSet hp).append (Ps₂.byStart p.val.finish
        <| heq ▸ finish_mem_FinishSet hp) fun b ↦ append_aux hsu (finish_mem_FinishSet hp)
        (heq ▸ finish_mem_FinishSet hp), ?_, ?_
      use p.val.finish, finish_mem_FinishSet hp
      sorry
    · sorry


end PathEnsemble

end disjoint

end Path
