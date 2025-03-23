import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic
import Kura.Dep.List


open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e f g : β}
namespace Graph


inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (W : Walk α β) : Walk α β

namespace Walk
variable {w w₁ : Walk α β} {w₂ : Walk α β}

def ValidOn (w : Walk α β) (G : Graph α β) (u v : α) : Prop :=
  match w with
  | nil x => x = u ∧ x = v ∧ x ∈ G.V
  | cons x e (nil y) => x = u ∧ y = v ∧ G.IsBetween e x y
  | cons x e (cons y f w) => x = u ∧ G.IsBetween e x y ∧ ValidOn (cons y f w) G y v

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

/-- Removes duplicate vertices from a walk, keeping only the first occurrence of each vertex. -/
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

@[simp] lemma nil_validOn (hx : x ∈ G.V) : (nil x : Walk α β).ValidOn G x x := by
  simp [ValidOn, hx]

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

lemma ValidOn.eq_left (h : (cons x e w).ValidOn G u v) : u = x := by
  match w with
  | nil y =>
    obtain ⟨rfl, rfl, hu⟩ := h
    simp
  | cons y f w' =>
    obtain ⟨rfl, h⟩ := h
    simp

@[simp] lemma cons_validOn (hw : w.ValidOn G y z) (he : G.IsBetween e x y) :
  (cons x e w).ValidOn G x z := by
  match w with
  | nil u =>
    obtain ⟨rfl, rfl, hu⟩ := hw
    refine ⟨rfl, rfl, he⟩
  | cons u f w' =>
    obtain rfl := hw.eq_left
    refine ⟨rfl, he, hw⟩

end Walk

open Walk

def IsBetween.Walk (_h : G.IsBetween e u v) : Walk α β := cons u e (nil v)

lemma IsBetween.walk_validOn (h : G.IsBetween e u v) : h.Walk.ValidOn G u v := by
  simp [Walk, ValidOn, h]

@[simp] lemma IsBetween.Walk.vx (h : G.IsBetween e u v): h.Walk.vx = [u, v] := rfl

@[simp] lemma IsBetween.Walk.edge (h : G.IsBetween e u v): h.Walk.edge = [e] := rfl

@[simp] lemma IsBetween.Walk.length (h : G.IsBetween e u v): h.Walk.length = 1 := rfl

/-- Given a graph adjacency, we can create a walk of length 1 -/
lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidOn G u v ∧ W.length = 1 := by
  obtain ⟨e, he⟩ := h
  use he.Walk, he.walk_validOn
  rfl

/-- Given a reflexive adjacency, we can create a walk of length at most 1 -/
lemma reflAdj.exist_walk (h : G.reflAdj u v) : ∃ (W : Walk α β), W.ValidOn G u v ∧ W.length ≤ 1 := by
  obtain hadj | ⟨rfl, hx⟩ := h
  · obtain ⟨W, hW, hlength⟩ := hadj.exist_walk
    use W, hW
    rw [hlength]
  · use nil u
    constructor
    · simp [ValidOn, hx]
    · simp

namespace Walk

lemma vx_ne_nil {w : Walk α β} : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

/-- Properties of append operation -/
@[simp]
lemma append_vx {w₁ w₂ : Walk α β} : (append w₁ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
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
lemma append_length {w₁ w₂ : Walk α β} : (append w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_length, ih]
    omega

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

-- /-- A subgraph inherits all valid walks -/
-- lemma validOn_le {G H : Graph α β} (h : w.ValidOn G u v) (hle : G ≤ H) : w.ValidOn H u v := sorry

end Walk

/-- A path is a walk with no duplicate vertices -/
def Path (α β : Type*) [DecidableEq α] := {w : Walk α β // w.vx.Nodup}

namespace Path
variable [DecidableEq α] {p : Path α β}


/-- A path is valid on a graph if its underlying walk is valid -/
def ValidOn (p : Path α β) (G : Graph α β) (u v : α) : Prop := p.val.ValidOn G u v

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

-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

section disjoint

variable {ι : Type*}

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint {u v : α} (Ps : ι → Path α β) : Prop :=
  ∀ i j x, x ∈ (Ps i).vx → x ∈ (Ps j).vx → i ≠ j → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (Ps : ι → Path α β) : Prop :=
  ∀ i j x, x ∈ (Ps i).vx → x ∈ (Ps j).vx → i = j

theorem Menger {k : ℕ} (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V) (hv : v ∈ G.V)
    (huv : ¬ G.Adj u v) (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
    ∃ Ps : Fin k → G.Path u v, InternallyDisjoint Ps := by
  classical
  by_cases heuv : ∃ e : β, e ∈ G.E ∧ ¬ G.Inc u e ∧ ¬ G.Inc v e
  · obtain ⟨e, he, hnuinc, hnvinc⟩ := heuv
    have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
    by_cases h :  ∀ (S : Set α), S.Finite → G{G.E \ {e}}.IsVxSeparator u v S → k ≤ S.ncard
    · have hG'term : G{G.E \ {e}}.E.ncard < G.E.ncard := by
        simp only [restrict_E]
        apply Set.ncard_lt_ncard ?_ Finite.edge_fin
        refine inter_ssubset_left_iff.mpr ?_
        rintro hsu
        have := hsu he
        simp at this
      have := Menger (G{G.E \ {e}}) u v hu hv (by contrapose! huv; exact huv.of_Adj_restrict ) h
      obtain ⟨Ps, hPs⟩ := this
      use fun i ↦ (Ps i).le hG'le
      intro i j x hx hx' hne
      refine hPs i j x ?_ ?_ hne
      · simpa using hx
      · simpa using hx'
    · simp only [not_forall, Classical.not_imp, not_le] at h
      obtain ⟨S, hSFin, hSsep, hcard⟩ := h
      obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
      let G'' := G /[hxy.inc_left.contractFun] {e}
      have hG''term : (G.E \ {e}).ncard < G.E.ncard := by
        apply Set.ncard_lt_ncard ?_ Finite.edge_fin
        simp [he]
      have := Menger G'' u v (by sorry) (by sorry) (by sorry) sorry (k := k)
      obtain ⟨Ps, hPs⟩ := this
      obtain ⟨i, hi, hieq⟩ : ∃! i, x ∈ (Ps i).vx := by
        sorry
      sorry
  · simp only [not_exists, not_and, not_not] at heuv
    by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
    · obtain ⟨x, hux, hxv⟩ := hadj
      let G' := G[G.V \ {x}]
      have hG'le : G' ≤ G := induce_le G Set.diff_subset
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
      have hG'Fin : G'.Finite := finite_of_le_finite hG'le
      obtain ⟨eux, heux⟩ := hux
      obtain ⟨exv, hexv⟩ := hxv
      obtain p : G.Path u v := (of_isBetween hexv ?_).cons heux ?_
      have := Menger G' (k := k-1) u v hu' hv' huv' ?_
      obtain ⟨Ps, hPs⟩ := this

      -- let Ps' : Fin k → G.Path u v := fun i ↦ Fin.cons sorry (fun i ↦ (Ps i).le hG'le) (i.cast (by sorry))
      -- use Fin.cons sorry (fun i ↦ (Ps i).le hG'le)
      sorry
    · sorry
termination_by G.E.ncard + k


end disjoint

end Path

-- /-- Convert a walk to a path by deduplicating vertices -/
-- def Walk.toPath [DecidableEq α] (w : Walk α β) : Path α β :=
--   ⟨w.dedup, dedup_vx_nodup w⟩
