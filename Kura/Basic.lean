-- import LeanCopilot
import Mathlib.Algebra.BigOperators.Sym
import Matroid.Axioms.Circuit

@[simp]
lemma Set.ext_iff_simp {α : Type*} {P Q : α → Prop} : {x | P x} = {x | Q x} ↔ ∀ x, P x ↔ Q x :=
  Set.ext_iff

variable {α β : Type*}

open Set Function

structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  Inc : α → β → Prop
  vx_mem_of_inc : ∀ ⦃v e⦄, Inc v e → v ∈ V
  edge_mem_of_inc : ∀ ⦃v e⦄, Inc v e → e ∈ E
  exists_vertex_inc : ∀ ⦃e⦄, e ∈ E → ∃ v, Inc v e
  not_hypergraph : ∀ ⦃x y z e⦄, Inc x e → Inc y e → Inc z e → x = y ∨ y = z ∨ x = z

-- @[repr]
-- instance : Repr (Graph α β) where
--   reprPrec G n := s!"Graph.mk {G.V} {G.E}"

variable {G : Graph α β} {u v w x y : α} {e f g : β}

namespace Graph

class Finite (G : Graph α β) : Prop where
  vx_fin : G.V.Finite
  edge_fin : G.E.Finite

instance instvxFinite [G.Finite] : G.V.Finite := Finite.vx_fin

instance instedgeFinite [G.Finite] : G.E.Finite := Finite.edge_fin

@[simp]
lemma Inc.vx_mem (h : G.Inc x e) : x ∈ G.V := G.vx_mem_of_inc h

@[simp]
lemma not_inc_of_not_vx_mem (h : x ∉ G.V) : ¬ G.Inc x e := by
  intro hinc
  exact h (G.vx_mem_of_inc hinc)

@[simp]
lemma Inc.edge_mem (h : G.Inc x e) : e ∈ G.E := G.edge_mem_of_inc h

@[simp]
lemma not_inc_of_not_edge_mem (h : e ∉ G.E) : ¬ G.Inc x e := by
  intro hinc
  exact h (G.edge_mem_of_inc hinc)

@[ext]
lemma ext {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (hInc : ∀ x e, G₁.Inc x e ↔ G₂.Inc x e) : G₁ = G₂ := by
  obtain ⟨hV, hE, hInc, hvx, hex, hex, hnh⟩ := G₁
  obtain ⟨hV', hE', hInc', hvx', hex', hex', hnh'⟩ := G₂
  simp only at hV hE hInc
  simp only [hV, hE, mk.injEq, true_and]
  ext x e
  exact hInc x e

abbrev IsLoop (G : Graph α β) (e : β) := ∃! x, G.Inc x e

lemma IsLoop.mem {G : Graph α β} {e : β} (h : G.IsLoop e) : e ∈ G.E := by
  obtain ⟨v, hv, h⟩ := h
  exact G.edge_mem_of_inc hv

lemma exist_two_of_not_loop {G : Graph α β} {e : β} (he : e ∈ G.E) (h : ¬G.IsLoop e) :
    ∃ x y, x ≠ y ∧ G.Inc x e ∧ G.Inc y e := by
  simp only [IsLoop, ExistsUnique, not_exists, not_and, not_forall, Classical.not_imp] at h
  choose v hv using G.exists_vertex_inc he
  choose w hw h using h v hv
  use v, w, ((ne_eq _ _).mpr h).symm

@[mk_iff]
structure IsBetween (G : Graph α β) (e : β) (x y : α) : Prop where
  inc_left : G.Inc x e
  inc_right : G.Inc y e
  isLoop_of_eq : x = y → G.IsLoop e

lemma IsBetween.symm (h : G.IsBetween e x y) : G.IsBetween e y x where
  inc_left := h.inc_right
  inc_right := h.inc_left
  isLoop_of_eq h' := h.isLoop_of_eq h'.symm

lemma IsBetween.comm : G.IsBetween e x y ↔ G.IsBetween e y x := by
  refine ⟨IsBetween.symm, IsBetween.symm⟩

lemma IsBetween.vx_mem_left (h : G.IsBetween e x y) : x ∈ G.V :=
  h.inc_left.vx_mem

lemma IsBetween.vx_mem_right (h : G.IsBetween e x y) : y ∈ G.V :=
  h.inc_right.vx_mem

lemma IsBetween.edge_mem (h : G.IsBetween e x y) : e ∈ G.E :=
  h.inc_left.edge_mem

lemma IsBetween.eq_of_inc (hBtw : G.IsBetween e x y) (hinc : G.Inc u e) : u = x ∨ u = y := by
  by_cases h : x = y
  · subst y
    obtain ⟨v, vhinc, heq⟩ := hBtw.isLoop_of_eq rfl
    have := heq u hinc
    have := heq x hBtw.inc_left
    subst u v
    exact Or.inl rfl
  · have := G.not_hypergraph hBtw.inc_left hinc hBtw.inc_right
    simp only [h, or_false] at this
    convert this using 1
    exact eq_comm

@[simp]
lemma forall_inc_iff {G : Graph α β} {P : α → Prop} {e : β} (hbtw : G.IsBetween e x y):
    (∀ x, G.Inc x e → P x) ↔ P x ∧ P y := by
  constructor
  · rintro h
    use h x hbtw.inc_left, h y hbtw.inc_right
  · rintro ⟨hx, hy⟩ u hu
    obtain rfl | rfl := hbtw.eq_of_inc hu <;> assumption

lemma IsBetween.sym2_eq (h1 : G.IsBetween e x y) (h2 : G.IsBetween e u v) :
    s(x, y) = s(u, v) := by
  by_cases h : x = y
  · subst y
    obtain ⟨k, hkinc, heq⟩ := h1.isLoop_of_eq rfl
    have := heq u h2.inc_left
    have := heq v h2.inc_right
    have := heq x h1.inc_left
    subst k u v
    rfl
  · have := G.not_hypergraph h1.inc_left h2.inc_left h1.inc_right
    simp only [h, or_false] at this
    obtain rfl | rfl := this
    · have := G.not_hypergraph h1.inc_left h1.inc_right h2.inc_right
      simp only [h, false_or] at this
      obtain rfl | rfl := this
      · rfl
      · obtain ⟨v, hinc, heq⟩ := h2.isLoop_of_eq rfl
        obtain rfl := heq x h1.inc_left
        obtain rfl := heq y h1.inc_right
        rfl
    · have := G.not_hypergraph h1.inc_left h2.inc_left h2.inc_right
      simp only [h, false_or] at this
      obtain rfl | rfl := this
      · obtain ⟨v, hinc, heq⟩ := h2.isLoop_of_eq rfl
        have := heq x h1.inc_left
        subst this
        have := heq u h1.inc_right
        subst this
        rfl
      · exact Sym2.eq_swap

lemma IsBetween.eq_or_eq_of_IsBetween (h : G.IsBetween e x y) (h' : G.IsBetween e u v) :
    x = u ∧ y = v ∨ x = v ∧ y = u := by
  have := h.sym2_eq h'
  simpa using this

lemma IsBetween.eq_of_IsBetween (h : G.IsBetween e x y) (h' : G.IsBetween e x u) : y = u := by
  obtain ⟨_h, rfl⟩ | ⟨rfl , rfl⟩ := h.eq_or_eq_of_IsBetween h' <;> rfl

@[simp]
lemma IsBetween.IsBetween_iff_eq_left (h : G.IsBetween e x y) : G.IsBetween e u y ↔ u = x :=
  ⟨fun h' => (h.symm.eq_of_IsBetween h'.symm).symm, fun h' => h' ▸ h⟩

@[simp]
lemma IsBetween.IsBetween_iff_eq_right (h : G.IsBetween e x y) : G.IsBetween e x u ↔ y = u :=
  ⟨fun h' => h.eq_of_IsBetween h', fun h' => h' ▸ h⟩

lemma IsBetween_iff : G.IsBetween e x y ↔ G.Inc x e ∧ G.Inc y e ∧ (x = y → G.IsLoop e) := by
  constructor
  · rintro h
    exact ⟨h.inc_left, h.inc_right, h.isLoop_of_eq⟩
  · rintro ⟨hincx, hincy, hloop⟩
    exact ⟨hincx, hincy, hloop⟩

lemma IsLoop_iff_IsBetween : G.IsLoop e ↔ ∃ x, G.IsBetween e x x := by
  constructor
  · rintro hloop
    have := hloop
    obtain ⟨v, hinc, hloop⟩ := hloop
    use v
    rw [IsBetween_iff]
    simp [this, hinc]
  · rintro ⟨x, h⟩
    use x, h.inc_left
    rw [forall_inc_iff h]
    tauto

@[simp]
lemma IsBetween.IsLoop_iff_eq (hbtw : G.IsBetween e x y) :
    G.IsLoop e ↔ x = y := by
  constructor
  · rintro hloop
    rw [IsLoop_iff_IsBetween] at hloop
    obtain ⟨v, hvv⟩ := hloop
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hvv.eq_or_eq_of_IsBetween hbtw <;> rfl
  · rintro rfl
    exact hbtw.isLoop_of_eq rfl


lemma exist_IsBetween_of_mem (he : e ∈ G.E) : ∃ x y, G.IsBetween e x y := by
  by_cases h : G.IsLoop e
  · have h' := h
    obtain ⟨v, hv, hloop⟩ := h
    use v, v
    rw [IsBetween_iff]
    refine ⟨hv, hv, fun _ ↦ h'⟩
  · obtain ⟨x, y, hne, hxinc, hyinc⟩ := exist_two_of_not_loop he h
    use x, y
    rw [IsBetween_iff]
    refine ⟨hxinc, hyinc, fun h ↦ False.elim (hne h)⟩

structure GraphIsBetween (α β : Type*) where
  V : Set α
  E : Set β
  isBtw : β → α → α → Prop
  hsymm : ∀ e x y, isBtw e x y → isBtw e y x
  vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V
  edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E
  exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y
  eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)

def ofGraphIsBetween (h : GraphIsBetween α β) : Graph α β where
  V := h.V
  E := h.E
  Inc v e := ∃ u, h.isBtw e v u
  vx_mem_of_inc := by
    rintro v e ⟨u, hbtw⟩
    exact h.vx_mem_of_isBtw_left e v u hbtw
  edge_mem_of_inc := by
    rintro v e ⟨u, hbtw⟩
    exact h.edge_mem_of_isBtw e v u hbtw
  exists_vertex_inc := by
    rintro e he
    exact h.exists_vertex_isBtw e he
  not_hypergraph := by
    rintro x y z e ⟨x', hx'⟩ ⟨y', hy'⟩ ⟨z', hz'⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_of_isBtw hx' hy' <;>
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_of_isBtw hz' hy' <;>
    tauto

@[simp]
lemma IsBetween.ofGraphIsBetween (G' : GraphIsBetween α β) :
    (ofGraphIsBetween G').IsBetween e x y ↔ G'.isBtw e x y := by
  constructor
  · rintro ⟨⟨x', hxbtw⟩, ⟨y', hybtw⟩, hloop⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := G'.eq_of_isBtw hxbtw hybtw
    · obtain ⟨z, hzinc, hzeq⟩ := hloop rfl
      obtain rfl := hzeq x' (by use x; exact G'.hsymm e x x' hxbtw)
      obtain rfl := hzeq x (by use x')
      assumption
    · exact hxbtw
  · rintro hbtw
    refine ⟨(by use y), ?_, ?_⟩
    · use x
      exact G'.hsymm _ _ _ hbtw
    · rintro rfl
      use x, (by use x)
      rintro y ⟨y', hybtw⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := G'.eq_of_isBtw hbtw hybtw <;> rfl

@[simp]
def toGraphIsBetween (G : Graph α β) : GraphIsBetween α β where
  V := G.V
  E := G.E
  isBtw := G.IsBetween
  hsymm _ _ _ := IsBetween.symm
  vx_mem_of_isBtw_left _ _ _ := IsBetween.vx_mem_left
  edge_mem_of_isBtw _ _ _ := IsBetween.edge_mem
  exists_vertex_isBtw _ he := exist_IsBetween_of_mem he
  eq_of_isBtw _ _ _ _ _ hxy huv := Sym2.eq_iff.mp (hxy.sym2_eq huv)


def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, G.IsBetween e x y

lemma Adj.comm : G.Adj x y ↔ G.Adj y x := by
  unfold Adj
  constructor <;>
  · rintro ⟨e, h⟩
    exact ⟨e, h.symm⟩

lemma Adj.symm (h : G.Adj x y) : G.Adj y x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ G.V := by
  obtain ⟨e, hinc, hif⟩ := h
  exact G.vx_mem_of_inc hinc

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ G.V := by
  rw [Adj.comm] at h
  exact Adj.mem_left h

@[simp]
lemma not_adj_of_not_mem_left (h : x ∉ G.V) : ¬G.Adj x y := by
  rintro ⟨e, hinc, hif⟩
  have hx' := G.vx_mem_of_inc hinc
  exact h hx'

@[simp]
lemma not_adj_of_not_mem_right (h : y ∉ G.V) : ¬G.Adj x y := by
  rw [Adj.comm]
  exact not_adj_of_not_mem_left h

@[simp]
lemma IsBetween.Adj (h : G.IsBetween e x y) : G.Adj x y := by
  use e

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc v e}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}




@[simp]
def reflAdj (G : Graph α β) (x y : α) :=
  G.Adj x y ∨ x = y ∧ x ∈ G.V
  -- fun x y ↦ ite (x = y) (h := Classical.dec _) (x ∈ G.V) (∃ e, G.Inc x e ∧ G.Inc y e)

lemma reflAdj.of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
  simp only [reflAdj, h, and_self, or_true]

@[simp]
lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj.of_vxMem h

lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
  apply h.imp
  · exact fun h ↦ h.symm
  · rintro ⟨rfl, hx⟩
    exact ⟨rfl, hx⟩

lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
  refine ⟨reflAdj.symm, reflAdj.symm⟩

lemma Inc.reflAdj_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.reflAdj x y := by
  by_cases hxy : x = y
  · subst y
    right
    exact ⟨rfl, hx.vx_mem⟩
  · left
    use e, hx, hy
    exact fun h ↦ (hxy h).elim

@[simp]
lemma reflAdj.mem_left (h : G.reflAdj x y) : x ∈ G.V := by
  apply h.elim
  · exact fun a ↦ a.mem_left
  · tauto

@[simp]
lemma reflAdj.mem_right (h : G.reflAdj x y) : y ∈ G.V := by
  rw [reflAdj.comm] at h
  exact h.mem_left

@[simp]
lemma IsBetween.reflAdj (h : G.IsBetween e x y) : G.reflAdj x y := by
  left
  use e

@[simp]
lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
  left
  exact h

lemma reflAdj.Adj_of_ne (h : G.reflAdj x y) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨e, h⟩ | ⟨rfl, hx⟩ := h
  · use e
  · contradiction

@[simp]
lemma reflAdj.Adj_iff_ne (hne : x ≠ y) : G.reflAdj x y ↔ G.Adj x y :=
  ⟨fun h => h.Adj_of_ne hne, fun h => h.reflAdj⟩

def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

@[simp]
lemma IsBetween.connected (h : G.IsBetween e x y) : G.Connected x y :=
  Relation.TransGen.single h.reflAdj

@[simp]
lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

@[simp]
lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| reflAdj.of_vxMem hx

lemma Inc.connected_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.Connected x y :=
  reflAdj.connected (hx.reflAdj_of_inc hy)

lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  rw [Relation.transGen_swap]
  congr! 1
  ext
  exact reflAdj.comm

@[simp]
lemma Connected.refl {G : Graph α β} {x : α} (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
  rwa [Connected.comm]

instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

lemma Connected.trans {G : Graph α β} {x y z : α} (hxy : G.Connected x y) (hyz : G.Connected y z) :
    G.Connected x z := Relation.TransGen.trans hxy hyz

instance : IsTrans α (G.Connected) := ⟨fun _ _ _ ↦ Connected.trans⟩

@[simp]
lemma Connected.mem_left (hconn : G.Connected x y) : x ∈ G.V := by
  simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
  obtain ⟨a, hradj, hTG⟩ := hconn
  exact hradj.mem_left

@[simp]
lemma Connected.mem_right (hconn : G.Connected x y) : y ∈ G.V := by
  rw [Connected.comm] at hconn
  exact hconn.mem_left

@[simp]
lemma not_connected_of_not_mem (h : x ∉ G.V) : ¬G.Connected x y := by
  contrapose! h
  exact h.mem_left

@[simp]
lemma not_connected_of_not_mem' (h : y ∉ G.V) : ¬G.Connected x y := by
  rw [Connected.comm]
  exact not_connected_of_not_mem h

@[simp]
lemma Connected.refl_iff {G : Graph α β} {x : α} : G.Connected x x ↔ x ∈ G.V := by
  refine ⟨?_, Connected.refl⟩
  rintro h
  exact h.mem_left

class Conn (G : Graph α β) : Prop where
  all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y



noncomputable def toSym2 (G : Graph α β) {e : β} (he : e ∈ G.E) : Sym2 α := by
  by_cases h : G.IsLoop e
  · choose v hv using h
    exact s(v, v)
  · choose x y h using (exist_two_of_not_loop he h)
    exact s(x, y)

lemma exists_mem_toSym2_iff_inc {G : Graph α β} {e : β} {y : α} :
    (∃ (he : e ∈ G.E), y ∈ G.toSym2 he) ↔ G.Inc y e := by
  by_cases h : G.IsLoop e
  · simp only [toSym2, h, ↓reduceDIte, Sym2.mem_iff, or_self, exists_prop]
    obtain ⟨hinc, heq⟩ := h.choose_spec
    constructor
    · rintro ⟨he, rfl⟩
      exact hinc
    · rintro h
      exact ⟨G.edge_mem_of_inc h, heq _ h⟩
  · simp only [toSym2, h, ↓reduceDIte, ne_eq, Sym2.mem_iff]
    constructor
    · rintro ⟨he, hor⟩
      obtain ⟨H1, H2, H3⟩ := (G.exist_two_of_not_loop he h).choose_spec.choose_spec
      cases hor <;> subst y <;> assumption
    · rintro hinc
      have he := G.edge_mem_of_inc hinc
      use he
      obtain ⟨H1, H2, H3⟩ := (G.exist_two_of_not_loop he h).choose_spec.choose_spec
      have heqor := G.not_hypergraph hinc H2 H3
      simpa only [ne_eq, H1, false_or] using heqor

@[simp]
lemma mem_toSym2_iff_inc {G : Graph α β} {e : β} {y : α} (he : e ∈ G.E):
    y ∈ G.toSym2 he ↔ G.Inc y e := by
  rw [← exists_mem_toSym2_iff_inc]
  simp only [he, exists_true_left]

@[simp]
lemma mem_toSym2_of_inc {G : Graph α β} {e : β} {y : α} (h : G.Inc y e) :
    y ∈ G.toSym2 (G.edge_mem_of_inc h) := by
  rw [← exists_mem_toSym2_iff_inc] at h
  obtain ⟨he, h⟩ := h
  exact h

@[simp]
lemma mem_of_mem_toSym2 {G : Graph α β} {e : β} {y : α} (he : e ∈ G.E) (h : y ∈ G.toSym2 he) :
    y ∈ G.V := by
  apply G.vx_mem_of_inc
  rw [← exists_mem_toSym2_iff_inc]
  use he


section edge_empty

lemma not_isBetween_of_E_empty (h : G.E = ∅) : ¬ G.IsBetween e x y := by
  contrapose! h
  use e, h.edge_mem

lemma not_adj_of_E_empty (h : G.E = ∅) : ¬ G.Adj x y := by
  rintro ⟨e, hbtw⟩
  exact (h ▸ hbtw.edge_mem : _)

@[simp]
lemma reflAdj_iff_eq_mem_of_E_empty (h : G.E = ∅) : G.reflAdj x y ↔ x = y ∧ x ∈ G.V:= by
  simp only [reflAdj, not_adj_of_E_empty h, false_or]

lemma connected_iff_reflAdj_of_E_empty (h : G.E = ∅) : G.Connected x y ↔ G.reflAdj x y := by
  constructor <;> rintro h
  · induction h with
    | single hradj => exact hradj
    | tail hconn hradj ih =>
      simp only [reflAdj, not_adj_of_E_empty h, false_or] at hradj ih ⊢
      obtain ⟨rfl, hc⟩ := hradj
      exact ih
  · exact reflAdj.connected h

@[simp]
lemma connected_iff_eq_mem_of_E_empty (h : G.E = ∅) : G.Connected x y ↔ x = y ∧ x ∈ G.V := by
  rw [← reflAdj_iff_eq_mem_of_E_empty h, connected_iff_reflAdj_of_E_empty h]

end edge_empty
section edge_subsingleton

@[simp]
lemma Adj.iff_IsBetween_of_E_singleton (h : G.E = {e}) : G.Adj x y ↔ G.IsBetween e x y := by
  constructor
  · rintro ⟨e, hbtw⟩
    exact (h ▸ hbtw.edge_mem) ▸ hbtw
  · exact fun h => ⟨e, h⟩

@[simp]
lemma Adj.iff_IsBetween_of_E_subsingleton (h : G.E ⊆ {e}) : G.Adj x y ↔ G.IsBetween e x y := by
  constructor
  · rintro ⟨e, hbtw⟩
    exact (h hbtw.edge_mem) ▸ hbtw
  · exact fun h => ⟨e, h⟩

@[simp]
lemma connected_iff_reflAdj_of_E_singleton (h : G.E = {e}) :
    G.Connected u v ↔ G.reflAdj u v := by
  refine ⟨fun hconn => ?_, (·.connected)⟩
  induction hconn with
  | single hradj => exact hradj
  | tail hconn hradj ih =>
    rename_i x y
    by_cases hxy : x = y
    · exact hxy ▸ ih
    · rw [reflAdj.Adj_iff_ne hxy, Adj.iff_IsBetween_of_E_singleton h] at hradj
      by_cases huy : u = y
      · exact huy ▸ reflAdj.refl ih.mem_left
      · by_cases hux : u = x
        · simp [huy, h, hradj, hux]
        · absurd huy
          rwa [reflAdj.Adj_iff_ne hux, Adj.iff_IsBetween_of_E_singleton h, IsBetween.comm,
            hradj.IsBetween_iff_eq_right, eq_comm] at ih

@[simp]
lemma connected_iff_reflAdj_of_E_subsingleton (h : G.E ⊆ {e}) :
    G.Connected u v ↔ G.reflAdj u v := by
  rw [subset_singleton_iff_eq] at h
  obtain hE | hE := h
  · exact connected_iff_reflAdj_of_E_empty hE
  · exact connected_iff_reflAdj_of_E_singleton hE

end edge_subsingleton


section Isolated

def Isolated (G : Graph α β) (v : α) := ∀ e, ¬ G.Inc v e

namespace Isolated

lemma not_adj_left (hisol : G.Isolated u) : ¬ G.Adj u v := by
  rintro ⟨e, hinc, hif⟩
  exact hisol e hinc

lemma not_adj_right (hisol : G.Isolated u) : ¬ G.Adj v u := by
  rw [Adj.comm]
  exact hisol.not_adj_left

lemma not_isBetween_left (hisol : G.Isolated u) : ¬ G.IsBetween e u v :=
  (hisol e ·.inc_left)

lemma not_isBetween_right (hisol : G.Isolated u) : ¬ G.IsBetween e v u :=
  (hisol e ·.inc_right)

lemma not_inc_of_E_empty (hE : G.E = ∅) : G.Isolated u := by
  intro e hinc
  exact (hE ▸ hinc.edge_mem : e ∈ ∅)

@[simp]
lemma reflAdj_iff (hisol : G.Isolated u) : G.reflAdj u v ↔ u = v ∧ u ∈ G.V := by
  simp only [reflAdj, not_adj_left hisol, false_or]

@[simp]
lemma connected_iff (hisol : G.Isolated u) : G.Connected u v ↔ u = v ∧ u ∈ G.V := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | single hradj => rwa [reflAdj_iff hisol] at hradj
    | tail w hconn ih =>
      obtain ⟨rfl, hu⟩ := ih
      rwa [reflAdj_iff hisol] at hconn
  · rintro ⟨rfl, h⟩
    exact connected_self h


end Isolated
