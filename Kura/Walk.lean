import Kura.Basic


open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
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

def vx {x y : α} : G.Walk x y → List α
| nil _hx => [x]
| cons _hbtw W => x :: W.vx

def edge {x y : α} : G.Walk x y → List β
| nil _ => []
| cons _hbtw W => by
  rename_i e
  exact e :: W.edge

def length {x y : α} : G.Walk x y → ℕ
| nil _ => 0
| cons _hbtw W => W.length + 1

@[simp]
lemma nil_length (hx : x ∈ G.V) : (nil hx).length = 0 := rfl

def of_isBetween (h : G.IsBetween e x y) : G.Walk x y :=
  cons h (nil h.vx_mem_right)

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

def concat {x y z : α} (w : G.Walk x y) {e : β} (h : G.IsBetween e y z) : G.Walk x z :=
  append w (of_isBetween h)

def reverse {x y : α} (w : G.Walk x y) : G.Walk y x :=
  match w with
  | nil h => nil h
  | cons hbtw W => append (reverse W) (of_isBetween hbtw.symm)

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

end Walk

-- structure Path (G : Graph α β) (u v : α) extends Walk G u v where
--   vx_nodup : vx.Nodup

-- namespace Path



-- end Path
