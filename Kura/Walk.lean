import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic


open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {x y z : α} {e f g : β}
namespace Graph


inductive Walk (G : Graph α β) : α → α → Type (max u_1 u_2) where
| nil ⦃u : α⦄ (h : u ∈ G.V) : G.Walk u u
| cons ⦃u v w : α⦄ ⦃e : β⦄ (he : G.IsBetween e w u) (W : G.Walk u v) : G.Walk w v

-- TODO: fix the implementation of IncList
-- structure IncList (G : Graph α β) (u v : α) where
--   vx : List α
--   edge : List β
--   hlen : vx.length = edge.length + 1
--   hInc1 : ∀ (i : ℕ) (h : i < edge.length),
--     G.Inc (vx[i]'(hlen ▸ Nat.lt_add_right 1 h)) edge[i]
--   hInc2 : ∀ (i : ℕ) (h : i < edge.length),
--     G.Inc (vx[i + 1]'(hlen ▸ (Nat.add_lt_add_right h 1))) edge[i]
--   hstart : vx.head (List.ne_nil_of_length_eq_add_one hlen) = u
--   hend : vx.getLast (List.ne_nil_of_length_eq_add_one hlen) = v

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
lemma of_isBetween_vx (h : G.IsBetween e x y) :
  (of_isBetween h).vx = [x, y] := rfl

@[simp]
lemma of_isBetween_length (h : G.IsBetween e x y) :
    (of_isBetween h).length = 1 := rfl

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

lemma append_vx :
  (append w₁ w₂).vx = w₁.vx ++ List.tail w₂.vx := by
  induction w₁ with
  | nil hx =>
    simp only [append, vx]
    cases w₂ with
    | nil hy => simp [List.tail_nil]
    | cons hbtw W =>
      simp only [vx, List.tail]
      rfl
  | cons hbtw W ih =>
    simp only [append, vx, List.cons_append]
    congr
    exact ih

lemma append_edge :
  (append w₁ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil hx =>
    simp only [append, edge]
    rfl
  | cons hbtw W ih =>
    simp only [append, edge]
    rw [List.cons_append]
    congr
    exact ih

lemma append_length :
  (append w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil hx =>
    simp [append, length, zero_add]
  | cons hbtw W ih =>
    simp [append, length]
    rw [ih]
    ring


def concat {x y z : α} (w : G.Walk x y) {e : β} (h : G.IsBetween e y z) : G.Walk x z :=
  append w (of_isBetween h)

/-- The vertices of a concat walk combine the vertices of the original walk with the endpoint. -/
lemma concat_vx (h : G.IsBetween e y z) :
  (concat w h).vx = w.vx ++ [z] := by
  simp [concat, append_vx, of_isBetween, vx, List.tail_cons]

/-- The edges of a concat walk combine the edges of the original walk with the new edge. -/
lemma concat_edge (h : G.IsBetween e y z) :
  (concat w h).edge = w.edge ++ [e] := by
  simp [concat, append_edge, of_isBetween, edge]

/-- The length of a concat walk is the length of the original walk plus one. -/
lemma concat_length (h : G.IsBetween e y z) :
  (concat w h).length = w.length + 1 := by
  simp [concat, append_length, of_isBetween_length]


def reverse {x y : α} (w : G.Walk x y) : G.Walk y x :=
  match w with
  | nil h => nil h
  | cons hbtw W => append (reverse W) (of_isBetween hbtw.symm)

/-- The vertices of a reversed walk are the reversal of the original walk's vertices. -/
lemma reverse_vx :
  (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil h => simp [reverse, vx, List.reverse_singleton]
  | cons hbtw W ih =>
    simp [reverse]
    rw [append_vx, ih]
    simp [vx, of_isBetween, List.reverse_cons]

/-- The edges of a reversed walk are the reversal of the original walk's edges. -/
lemma reverse_edge :
  (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil h => simp [reverse, edge, List.reverse_nil]
  | cons hbtw W ih =>
    simp [reverse]
    rw [append_edge, ih]
    simp [edge, of_isBetween, List.reverse_cons]

/-- The length of a reversed walk equals the length of the original walk. -/
lemma reverse_length :
  (reverse w).length = w.length := by
  induction w with
  | nil h =>
    simp [reverse, length]
  | cons hbtw W ih =>
    simp [reverse, append, length]
    rw [append_length, of_isBetween_length, ih]


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

/-- Concatenating a walk with an edge preserves connectedness. -/
lemma concat_connected (w : G.Walk x y) (h : G.IsBetween e y z) :
  G.Connected x z := by
  apply (concat w h).connected

def le {x y : α} {H : Graph α β} (w : G.Walk x y) (hle : G ≤ H) : H.Walk x y :=
  match w with
  | nil h => nil (vx_subset_of_le hle h)
  | cons hbtw W => cons (hbtw.le hle) (W.le hle)

lemma le_vx {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).vx = w.vx := by
  match w with
  | nil h => simp [le, nil_vx]
  | cons hbtw W =>
    simp only [le, cons_vx, List.cons.injEq, true_and]
    exact W.le_vx hle

lemma le_edge {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).edge = w.edge := by
  match w with
  | nil h => simp [le, nil_edge]
  | cons hbtw W =>
    simp only [le, cons_edge, List.cons.injEq, true_and]
    exact W.le_edge hle

lemma le_length {x y : α} {w : G.Walk x y} (hle : G ≤ H) : (le w hle).length = w.length := by
  match w with
  | nil h => simp [le, nil_length]
  | cons hbtw W =>
    simp only [le, cons_length, true_and]
    have := W.le_length hle
    exact congrFun (congrArg _ this) 1

@[simp]
def IsPath (W : G.Walk x y) : Prop := W.vx.Nodup


end Walk


abbrev Path (x y : α) := {P : G.Walk x y // P.IsPath}

namespace Path
variable {p p₁ : G.Path x y} {p₂ : G.Path y z}

def vx {x y : α} : G.Path x y → List α
| ⟨W, _hW⟩ => W.vx

def edge {x y : α} : G.Path x y → List β
| ⟨W, _hW⟩ => W.edge

def length {x y : α} : G.Path x y → ℕ
| ⟨W, _hW⟩ => W.length

def nil (hx : x ∈ G.V) : G.Path x x := ⟨Walk.nil hx, by simp [Walk.IsPath]⟩


def le {x y : α} {H : Graph α β} (p : H.Path x y) (hle : H ≤ G) : G.Path x y :=
  ⟨p.1.le hle, by simp only [Walk.IsPath, Walk.le_vx]; exact p.2⟩

@[simp]
lemma le_vx {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).vx = p.vx := by
  simp [le, vx, Walk.le_vx]

@[simp]
lemma le_edge {x y : α} {p : G.Path x y} (hle : G ≤ H) : (le p hle).edge = p.edge := by
  simp [le, edge, Walk.le_edge]



section disjoint

variable {ι : Type*}

def InternallyDisjoint {G : Graph α β} {u v : α} (Ps : ι → G.Path u v) : Prop :=
  ∀ i j x, x ∈ (Ps i).vx → x ∈ (Ps j).vx → i ≠ j → x = u ∨ x = v

def Disjoint (u v : ι → α) (Ps : ∀ i, G.Path (u i) (v i)) : Prop :=
  ∀ i j x, x ∈ (Ps i).vx → x ∈ (Ps j).vx → i = j

theorem Menger {k : ℕ} (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V) (hv : v ∈ G.V)
    (huv : ¬ G.Adj u v) (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
    ∃ Ps : Fin k → G.Path u v, InternallyDisjoint Ps := by
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
        let G'' :=
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
