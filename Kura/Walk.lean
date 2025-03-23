import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic
import Kura.Dep.List


open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {x y z : α} {e f g : β}
namespace Graph


inductive Walk (G : Graph α β) : α → α → Type (max u_1 u_2) where
| nil ⦃u : α⦄ (h : u ∈ G.V) : G.Walk u u
| cons ⦃u v w : α⦄ ⦃e : β⦄ (he : G.IsBetween e w u) (W : G.Walk u v) : G.Walk w v

namespace Walk
variable {w w₁ : G.Walk x y} {w₂ : G.Walk y z}

def vx {x y : α} : G.Walk x y → List α
| nil _hx => [x]
| cons _hbtw W => x :: W.vx

@[simp]
lemma nil_vx (hx : x ∈ G.V) : (nil hx).vx = [x] := rfl

@[simp]
lemma cons_vx (hbtw : G.IsBetween e x y) (W : G.Walk y z) :
  (cons hbtw W).vx = x :: W.vx := rfl

def edge {x y : α} : G.Walk x y → List β
| nil _ => []
| cons _hbtw W => by
  rename_i e
  exact e :: W.edge

@[simp]
lemma nil_edge (hx : x ∈ G.V) : (nil hx).edge = [] := rfl

@[simp]
lemma cons_edge (hbtw : G.IsBetween e x y) (W : G.Walk y z) :
  (cons hbtw W).edge = e :: W.edge := rfl

def length {x y : α} : G.Walk x y → ℕ
| nil _ => 0
| cons _hbtw W => W.length + 1

@[simp]
lemma nil_length (hx : x ∈ G.V) : (nil hx).length = 0 := rfl

@[simp]
lemma cons_length (hbtw : G.IsBetween e x y) (W : G.Walk y z) :
  (cons hbtw W).length = W.length + 1 := rfl

def of_isBetween (h : G.IsBetween e x y) : G.Walk x y :=
  cons h (nil h.vx_mem_right)

@[simp]
lemma of_isBetween_vx (h : G.IsBetween e x y) : (of_isBetween h).vx = [x, y] := rfl

@[simp]
lemma of_isBetween_edge (h : G.IsBetween e x y) : (of_isBetween h).edge = [e] := rfl

@[simp]
lemma of_isBetween_length (h : G.IsBetween e x y) : (of_isBetween h).length = 1 := rfl

lemma of_adj (h : G.Adj x y) : ∃ (W : G.Walk x y), W.length = 1 := by
  obtain ⟨e, he⟩ := h
  use of_isBetween he
  exact rfl

lemma of_reflAdj (h : G.reflAdj x y) : ∃ (W : G.Walk x y), W.length ≤ 1 := by
  obtain hadj | ⟨rfl, hx⟩ := h
  · obtain ⟨W, hW⟩ := of_adj hadj
    use W
    rw [hW]
  · use nil hx
    simp only [nil_length, _root_.zero_le]


def append {x y z : α} (w₁ : G.Walk x y) (w₂ : G.Walk y z) : G.Walk x z :=
  match w₁ with
  | nil h => w₂
  | cons hbtw W => cons hbtw (append W w₂)

@[simp]
lemma append_vx :
  (append w₁ w₂).vx = w₁.vx ++ List.tail w₂.vx := by
  induction w₁ with
  | nil hx =>
    match w₂ with
    | nil hy => simp [append]
    | cons hbtw W => simp [append]
  | cons hbtw W ih => simp [append, ih]

@[simp]
lemma append_edge :
  (append w₁ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil hx => simp [append]
  | cons hbtw W ih => simp [append, ih]

@[simp]
lemma append_length :
  (append w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil hx => simp [append]
  | cons hbtw W ih =>
    simp [append, ih]
    ring


def concat {x y z : α} (w : G.Walk x y) {e : β} (h : G.IsBetween e y z) : G.Walk x z :=
  append w (of_isBetween h)

/-- The vertices of a concat walk combine the vertices of the original walk with the endpoint. -/
@[simp]
lemma concat_vx (h : G.IsBetween e y z) :
  (concat w h).vx = w.vx ++ [z] := by
  simp [concat]

/-- The edges of a concat walk combine the edges of the original walk with the new edge. -/
@[simp]
lemma concat_edge (h : G.IsBetween e y z) : (concat w h).edge = w.edge ++ [e] := by
  simp [concat]

/-- The length of a concat walk is the length of the original walk plus one. -/
@[simp]
lemma concat_length (h : G.IsBetween e y z) : (concat w h).length = w.length + 1 := by
  simp [concat]


def reverse {x y : α} (w : G.Walk x y) : G.Walk y x :=
  match w with
  | nil h => nil h
  | cons hbtw W => append (reverse W) (of_isBetween hbtw.symm)

/-- The vertices of a reversed walk are the reversal of the original walk's vertices. -/
@[simp]
lemma reverse_vx : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil h => simp [reverse]
  | cons hbtw W ih => simp [reverse, ih]

/-- The edges of a reversed walk are the reversal of the original walk's edges. -/
@[simp]
lemma reverse_edge : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil h => simp [reverse]
  | cons hbtw W ih => simp [reverse, ih]

/-- The length of a reversed walk equals the length of the original walk. -/
@[simp]
lemma reverse_length : (reverse w).length = w.length := by
  induction w with
  | nil h => simp [reverse]
  | cons hbtw W ih => simp [reverse, ih]

/-- Given a walk, and a vertex that is in the walk, we can construct a walk from that vertex
to the end of the walk.
In the presence of multiple occurrences of the vertex in the walk, this function will return the
shortest possible walk. (i.e. start from the last occurrence of the vertex)
-/
def startAt [DecidableEq α] {x y z : α} (w : G.Walk x y) (hz : z ∈ w.vx) : G.Walk z y := by
  match w with
  | nil hx =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hz
    subst hz
    exact nil hx
  | cons hbtw W =>
    if hin : z ∈ W.vx then
      exact startAt W hin
    else
      simp only [cons_vx, mem_cons, hin, or_false] at hz
      subst z
      exact cons hbtw W

-- lemma startAt_vx_rtakeWhlie [DecidableEq α] {x y z : α} (w : G.Walk x y) (hz : z ∈ w.vx) :
--   (w.startAt hz).vx = z :: w.vx.rtakeWhile (· ≠ z) := by
--   induction w with
--   | nil =>
--     simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hz
--     subst hz
--     simp [startAt]
--   | cons hbtw W ih =>
--     unfold startAt
--     split_ifs with hin
--     · rw [ih hin, cons_vx, eq_comm]
--       congr 1
--       apply List.rtakeWhlie_cons_of_mem_neg (hain := hin)
--       simp
--     · simp only [ne_eq, decide_not, cons_vx]
--       expose_names
--       suffices (cons hbtw W).vx = z :: rtakeWhile (fun x ↦ !decide (x = z)) (w :: W.vx) by
--         convert this using 1

--         sorry
--       sorry




/-- Given a walk, and a vertex that is in the walk, we can construct a walk from the start of the
walk to that vertex.
In the presence of multiple occurrences of the vertex in the walk, this function will return the
shortest possible walk. (i.e. stop at the first occurrence of the vertex)
-/
def endAt [DecidableEq α] {x y z : α} (w : G.Walk x y) (hz : z ∈ w.vx) : G.Walk x z :=
  (w.reverse.startAt (by simpa)).reverse

-- def dedup [DecidableEq α] {x y : α} (w : G.Walk x y) : G.Walk x y :=
--   match w with
--   | nil hx => nil hx
--   | cons hbtw W =>
--     if hin : x ∈ W.vx
--     then (W.startAt hin).dedup
--     else cons hbtw (dedup W)

-- lemma dedup_vx_nodup [DecidableEq α] (w : G.Walk x y) : w.dedup.vx.Nodup := by
--   match w with
--   | nil hx => simp [dedup]
--   | cons hbtw W =>
--     simp only [dedup]
--     split_ifs with hin
--     · simp [startAt]
--     · simp



lemma connected (W : G.Walk x y) : G.Connected x y := by
  induction W with
  | nil h => exact Connected.refl h
  | cons W hbtw ih =>
    rename_i u v w e
    refine Connected.trans ?_ ih
    refine Adj.connected ?_
    use e

lemma connected_iff : G.Connected x y ↔ Nonempty (G.Walk x y) := by
  refine ⟨fun h ↦ ?_, fun a ↦ a.some.connected⟩
  induction h with
  | single hradj =>
    obtain ⟨W, hW⟩ := of_reflAdj hradj
    use W
  | tail hConn hrAdj ih =>
    obtain ⟨W', hW'⟩ := of_reflAdj hrAdj
    use ih.some.append W'

def le {x y : α} {H : Graph α β} (w : G.Walk x y) (hle : G ≤ H) : H.Walk x y :=
  match w with
  | nil h => nil (vx_subset_of_le hle h)
  | cons hbtw W => cons (hbtw.le hle) (W.le hle)

@[simp]
lemma le_vx {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).vx = w.vx := by
  match w with
  | nil h => simp [le, nil_vx]
  | cons hbtw W =>
    simp only [le, cons_vx, List.cons.injEq, true_and]
    exact W.le_vx hle

@[simp]
lemma le_edge {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).edge = w.edge := by
  match w with
  | nil h => simp [le]
  | cons hbtw W =>
    simp only [le, cons_edge, List.cons.injEq, true_and]
    exact W.le_edge hle

@[simp]
lemma le_length {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).length = w.length := by
  match w with
  | nil h => simp [le]
  | cons hbtw W =>
    simp only [le, cons_length, true_and]
    have := W.le_length hle
    exact congrFun (congrArg _ this) 1

-- def contract {α' : Type*} {x' y' : α'} {f : α → α'} {C : Set β} (w : (G /[f] C).Walk x' y')
--     (hx : f x = x') (hy : f y = y') : G.Walk x y := by
--   match w with
--   | nil hx' =>
--     subst x'

--     subst hx'
--     exact nil hx
--   | cons hbtw W =>
--     simp only [cons_vx, cons_edge, cons_length]


end Walk


abbrev Path (G : Graph α β) (x y : α) := {P : G.Walk x y // P.vx.Nodup}

namespace Path
variable {p p₁ : G.Path x y} {p₂ : G.Path y z}

@[simp]
def vx {x y : α} : G.Path x y → List α
| ⟨W, _hW⟩ => W.vx

@[simp]
def edge {x y : α} : G.Path x y → List β
| ⟨W, _hW⟩ => W.edge

@[simp]
def length {x y : α} : G.Path x y → ℕ
| ⟨W, _hW⟩ => W.length

def nil (hx : x ∈ G.V) : G.Path x x := ⟨Walk.nil hx, by simp⟩

@[simp]
lemma nil_val (hx : x ∈ G.V) : (nil hx).1 = Walk.nil hx := rfl

@[simp]
lemma nil_vx (hx : x ∈ G.V) : (nil hx).vx = [x] := rfl

@[simp]
lemma nil_edge (hx : x ∈ G.V) : (nil hx).edge = [] := rfl

@[simp]
lemma nil_length (hx : x ∈ G.V) : (nil hx).length = 0 := rfl

/-- Create a path from a single edge between two vertices. -/
def of_isBetween (h : G.IsBetween e x y) (hnotLoop : x ≠ y) : G.Path x y :=
  ⟨Walk.of_isBetween h, by simpa⟩

@[simp]
lemma of_isBetween_val (h : G.IsBetween e x y) (hnotLoop : x ≠ y):
  (of_isBetween h hnotLoop).1 = Walk.of_isBetween h := rfl

@[simp]
lemma of_isBetween_vx (h : G.IsBetween e x y) (hnotLoop : x ≠ y):
  (of_isBetween h hnotLoop).vx = [x, y] := rfl

@[simp]
lemma of_isBetween_edge (h : G.IsBetween e x y) (hnotLoop : x ≠ y):
  (of_isBetween h hnotLoop).edge = [e] := rfl

@[simp]
lemma of_isBetween_length (h : G.IsBetween e x y) (hnotLoop : x ≠ y):
  (of_isBetween h hnotLoop).length = 1 := rfl

/-- If two vertices are adjacent, there exists a path of length 1 between them. -/
lemma of_adj (h : G.Adj x y) (hnotLoop : x ≠ y):
    ∃ (P : G.Path x y), P.length = 1 ∧ P.vx = [x, y] := by
  obtain ⟨e, he⟩ := h
  use of_isBetween he hnotLoop, ?_
  · simp
  · apply of_isBetween_length

/-- If two vertices are reflexively adjacent, there exists a path of length at most 1 between them. -/
lemma of_reflAdj (h : G.reflAdj x y) : ∃ (P : G.Path x y), P.length ≤ 1 ∧ x ∈ P.vx ∧ y ∈ P.vx := by
  by_cases hxy : x = y
  · -- If x = y, use the nil path
    subst hxy
    refine ⟨nil h.mem_left, ?_⟩
    constructor
    · -- nil length is 0, which is ≤ 1
      simp only [nil_length]
      exact zero_le_one
    · -- x and y are in the vertices list (both are x)
      simp only [nil_vx, List.mem_singleton]
      exact ⟨True.intro, True.intro⟩
  · -- If x ≠ y, then they must be adjacent with an edge
    rcases h with hadj | ⟨rfl, _⟩
    · -- They're adjacent through an edge
      obtain ⟨e, he⟩ := hadj
      refine ⟨of_isBetween he hxy, ?_⟩
      constructor
      · -- Length is exactly 1
        simp only [of_isBetween_length]
        exact le_refl 1
      · -- Both vertices are in the path
        simp only [of_isBetween_vx, List.mem_cons, List.mem_singleton]
        exact ⟨Or.inl True.intro, Or.inr (Or.inl True.intro)⟩
    · -- This case is impossible since x ≠ y but rfl : x = y
      contradiction

def cons (h : G.IsBetween e x y) (p : G.Path y z) (hx : x ∉ p.vx) : G.Path x z :=
  ⟨Walk.cons h (p.1), by simpa [p.2]⟩

@[simp]
lemma cons_val (h : G.IsBetween e x y) (p : G.Path y z) (hx : x ∉ p.vx) :
  (cons h p hx).1 = Walk.cons h p.1 := rfl

@[simp]
lemma cons_vx (h : G.IsBetween e x y) (p : G.Path y z) (hx : x ∉ p.vx) :
  (cons h p hx).vx = x :: p.vx := by
  simp [cons]

@[simp]
lemma cons_edge (h : G.IsBetween e x y) (p : G.Path y z) (hx : x ∉ p.vx) :
  (cons h p hx).edge = e :: p.edge := by
  simp [cons]

@[simp]
lemma cons_length (h : G.IsBetween e x y) (p : G.Path y z) (hx : x ∉ p.vx) :
  (cons h p hx).length = p.length + 1 := by
  simp [cons]

/-- Extend a path by an edge while maintaining the path property. -/
def concat (p : G.Path x y) (h : G.IsBetween e y z) (hz : z ∉ p.vx) : G.Path x z :=
  ⟨p.1.concat h, by
    simp only [Walk.concat_vx]
    rw [List.nodup_append]
    simpa [p.2]⟩

@[simp]
lemma concat_val (p : G.Path x y) (h : G.IsBetween e y z) (hz : z ∉ p.vx) :
  (concat p h hz).1 = p.1.concat h := rfl

@[simp]
lemma concat_vx (p : G.Path x y) (h : G.IsBetween e y z) (hz : z ∉ p.vx) :
  (concat p h hz).vx = p.vx ++ [z] := by
  simp [concat]

@[simp]
lemma concat_edge (p : G.Path x y) (h : G.IsBetween e y z) (hz : z ∉ p.vx) :
  (concat p h hz).edge = p.edge ++ [e] := by
  simp [concat]

@[simp]
lemma concat_length (p : G.Path x y) (h : G.IsBetween e y z) (hz : z ∉ p.vx) :
  (concat p h hz).length = p.length + 1 := by
  simp [concat]

/-- Create a reversed path from one that goes from x to y to one from y to x -/
def reverse (p : G.Path x y) : G.Path y x :=
  ⟨p.1.reverse, by simp [Walk.reverse_vx]; exact p.2⟩

@[simp]
lemma reverse_val (p : G.Path x y) : (reverse p).1 = p.1.reverse := rfl

@[simp]
lemma reverse_vx (p : G.Path x y) : (reverse p).vx = p.vx.reverse := by
  obtain ⟨W, hW⟩ := p
  simp only [vx, reverse]
  exact Walk.reverse_vx

@[simp]
lemma reverse_edge (p : G.Path x y) : (reverse p).edge = p.edge.reverse := by
  obtain ⟨W, hW⟩ := p
  simp only [edge, reverse]
  exact Walk.reverse_edge

@[simp]
lemma reverse_length (p : G.Path x y) : (reverse p).length = p.length := by
  obtain ⟨W, hW⟩ := p
  simp only [length, reverse]
  exact Walk.reverse_length

def le {H : Graph α β} (p : G.Path x y) (hle : G ≤ H) : H.Path x y :=
  ⟨p.1.le hle, by simp only [Walk.le_vx]; exact p.2⟩

@[simp]
lemma le_val (hle : G ≤ H) : (le p hle).1 = p.1.le hle := rfl

@[simp]
lemma le_vx (hle : G ≤ H) : (le p hle).vx = p.vx := by
  simp [le, vx, Walk.le_vx]

@[simp]
lemma le_edge (hle : G ≤ H) : (le p hle).edge = p.edge := by
  simp [le, edge, Walk.le_edge]

@[simp]
lemma le_length (hle : G ≤ H) : (le p hle).length = p.length := by
  simp [le, length, Walk.le_length]

def contract {α' : Type*} {f : α → α'} {C : Set β} (p : (G /[f] C).Path (f x) (f y)) : G.Path x y :=
  sorry

end Path

-- def Walk.toPath [DecidableEq α] {x y : α} : G.Walk x y → G.Path x y := by
--   intro w
--   use w.dedup
--   sorry

namespace Path

/-- Check if a path can be appended to another while maintaining the path property. -/
def appendable (p₁ : G.Path x y) (p₂ : G.Path y z) : Prop :=
  ∀ w, w ∈ p₁.vx.tail → w ∈ p₂.vx → w = y

/-- Append two paths if they can be appended while maintaining the path property. -/
def append (p₁ : G.Path x y) (p₂ : G.Path y z) (h : appendable p₁ p₂) : G.Path x z := sorry

-- @[simp]
-- lemma append_val (p₁ : G.Path x y) (p₂ : G.Path y z) (h : appendable p₁ p₂) :
--   (append p₁ p₂ h).1 = append p₁.1 p₂.1 (by simpa using h) := rfl

lemma append_vx (p₁ : G.Path x y) (p₂ : G.Path y z) (h : appendable p₁ p₂) :
  (append p₁ p₂ h).vx = p₁.vx ++ p₂.vx.tail := sorry

lemma append_edge (p₁ : G.Path x y) (p₂ : G.Path y z) (h : appendable p₁ p₂) :
  (append p₁ p₂ h).edge = p₁.edge ++ p₂.edge := sorry

lemma append_length (p₁ : G.Path x y) (p₂ : G.Path y z) (h : appendable p₁ p₂) :
  (append p₁ p₂ h).length = p₁.length + p₂.length := sorry




/-- Paths establish connectivity between their endpoints. -/
lemma connected (p : G.Path x y) : G.Connected x y :=
  p.1.connected

-- /-- There is a path between two vertices if and only if they are connected. -/
-- lemma connected_iff : G.Connected x y ↔ Nonempty (G.Path x y) := by
--   constructor
--   · intro hConn
--     induction hConn with
--     | single hradj =>
--       expose_names
--       by_cases hxb : x = b
--       · subst b
--         use nil hradj.mem_left
--         simp
--       · have : G.Adj x b := by exact reflAdj.Adj_of_ne hradj hxb



--       use of_isBetween hradj hW.2
--     | tail hconn hradj ih =>
--       obtain ⟨W, hW⟩ := of_reflAdj hradj
--       use ih.some.append (of_isBetween hradj hW.2)
--       simpa using hW.1

--   · intro hPath
--     -- From path to connectivity: This direction is easy
--     exact hPath.some.connected

section disjoint

variable {ι : Type*}

def InternallyDisjoint {G : Graph α β} {u v : α} (Ps : ι → G.Path u v) : Prop :=
  ∀ i j x, x ∈ (Ps i).vx → x ∈ (Ps j).vx → i ≠ j → x = u ∨ x = v

def Disjoint (u v : ι → α) (Ps : ∀ i, G.Path (u i) (v i)) : Prop :=
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
      have hG'term : (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard + (k - 1) <
        G.E.ncard + k := by sorry
      have := Menger G' (k := k-1) u v hu' hv' huv' ?_
      obtain ⟨Ps, hPs⟩ := this

      -- let Ps' : Fin k → G.Path u v := fun i ↦ Fin.cons sorry (fun i ↦ (Ps i).le hG'le) (i.cast (by sorry))
      -- use Fin.cons sorry (fun i ↦ (Ps i).le hG'le)
      sorry
      sorry
    · sorry
termination_by G.E.ncard + k


end disjoint

end Path




-- end Path
