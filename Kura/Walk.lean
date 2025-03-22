import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic


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

end Walk


abbrev Path (x y : α) := {P : G.Walk x y // P.vx.Nodup}

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

def le {x y : α} {H : Graph α β} (p : G.Path x y) (hle : G ≤ H) : H.Path x y :=
  ⟨p.1.le hle, by simp only [Walk.le_vx]; exact p.2⟩

@[simp]
lemma le_val {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).1 = p.1.le hle := rfl

@[simp]
lemma le_vx {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).vx = p.vx := by
  simp [le, vx, Walk.le_vx]

@[simp]
lemma le_edge {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).edge = p.edge := by
  simp [le, edge, Walk.le_edge]

@[simp]
lemma le_length {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).length = p.length := by
  simp [le, length, Walk.le_length]

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

/-- Paths establish connectivity between their endpoints. -/
lemma connected (p : G.Path x y) : G.Connected x y :=
  p.1.connected

/-- There is a path between two vertices if and only if they are connected. -/
lemma connected_iff : G.Connected x y ↔ Nonempty (G.Path x y) := by
  constructor
  · intro hConn
    induction hConn with
    | single hradj =>
      expose_names
      by_cases hxb : x = b
      · subst b
        use nil hradj.mem_left
        simp
      · have : G.Adj x b := by exact?


      use of_isBetween hradj hW.2
    | tail hconn hradj ih =>
      obtain ⟨W, hW⟩ := of_reflAdj hradj
      use ih.some.append (of_isBetween hradj hW.2)
      simpa using hW.1

  · intro hPath
    -- From path to connectivity: This direction is easy
    exact hPath.some.connected

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
  induction k generalizing G with
  | zero =>
    use fun a ↦ Fin.elim0 a
    simp [InternallyDisjoint]
  | succ k ih =>
    by_cases heuv : ∃ e : β, e ∈ G.E ∧¬ G.Inc u e ∧ ¬ G.Inc v e
    · obtain ⟨e, he, hnuinc, hnvinc⟩ := heuv
      let G' := G{{e}ᶜ}
      have hG'le : G' ≤ G := restrict_le G {e}ᶜ
      by_cases h :  ∀ (S : Set α), S.Finite → G'.IsVxSeparator u v S → k+1 ≤ S.ncard
      · obtain ⟨Ps, hPs⟩ := Menger G' u v (by sorry) (by sorry) (by sorry) h
        use fun i ↦ (Ps i).le hG'le
        intro i j x hx hx' hne
        refine hPs i j x ?_ ?_ hne
        · simpa using hx
        · simpa using hx'
      · simp only [not_forall, Classical.not_imp, not_le] at h
        obtain ⟨S, hSFin, hSsep, hcard⟩ := h
        obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
        let G'' := G /[hxy.inc_left.contractFun] {e}
        have := Menger G'' u v (by sorry) (by sorry) (by sorry) ?_
        sorry
      -- specialize ih G' hu hv (by rintro hadj; exact huv (hadj.le hG'le)) ?_
      -- · rintro S hSFin hS
      --   obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
      --   have := (h (insert x S) (hSFin.insert x) ?_).trans (Set.ncard_insert_le _ _)
      --   omega
      --   · refine ⟨?_, ?_, ?_⟩
      --     · simp only [Set.mem_insert_iff, hS.not_mem_left, or_false]
      --       rintro rfl
      --       exact hnuinc (hxy.inc_left)
      --     · simp only [Set.mem_insert_iff, hS.not_mem_right, or_false]
      --       rintro rfl
      --       exact hnvinc (hxy.inc_left)
      --     · rintro hconn
      --       refine hS.not_connected (hconn.le ⟨?_, ?_, ?_⟩)
      --       · rintro a
      --         simp only [induce_V, Set.mem_inter_iff, mem_diff, Set.mem_insert_iff, restrict_V, G']
      --         tauto
      --       · rintro e'
      --         simp only [induce_E, mem_diff, Set.mem_insert_iff, not_or, Set.mem_inter_iff,
      --           mem_setOf_eq, restrict_V, restrict_E, restrict_inc, mem_compl_iff,
      --           mem_singleton_iff, and_imp, G']
      --         rintro he' h1
      --         use ⟨he', ?_⟩
      --         rintro a hainc hne
      --         specialize h1 a hainc
      --         exact ⟨h1.1, h1.2.2⟩
      --         · rintro rfl
      --           obtain ⟨H1, H2, H3⟩ := h1 x hxy.inc_left
      --           simp at H2
      --       · rintro a

      --         sorry
    · simp only [not_exists, not_and, not_not] at heuv
      by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
      · obtain ⟨x, huv, hxv⟩ := hadj
        let G' := G[{x}ᶜ]
        have hG'le : G' ≤ G := induce_le G {x}ᶜ
        have hu' : u ∈ G'.V := by sorry
        have hv' : v ∈ G'.V := by sorry
        have huv' : ¬ G'.Adj u v := by sorry
        have := Menger G' (k := k) u v hu' hv' huv' ?_
        obtain ⟨Ps, hPs⟩ := this
        use Fin.cons sorry (fun i ↦ (Ps i).le hG'le)
        sorry
        sorry
      --   obtain ⟨Ps, hPs⟩ := Menger G' u v (k := k) hu' hv' huv' ?_
      --   sorry
      · sorry



end disjoint

end Path


-- structure Path (G : Graph α β) (u v : α) extends Walk G u v where
--   vx_nodup : vx.Nodup

-- namespace Path



-- end Path
