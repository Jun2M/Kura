import Kura.Basic

open Set Function

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e f g : β}

namespace Graph

section edge_empty

@[simp]
lemma incFun_eq_zero_of_E_empty (h : G.E = ∅) : G.incFun = 0 := by
  ext e v
  simp only [h, mem_empty_iff_false, not_false_eq_true, incFun_of_not_mem_edgeSet, Finsupp.coe_zero,
    Pi.zero_apply]

@[simp]
lemma not_inc_of_E_empty (h : G.E = ∅) : ¬ G.Inc e v := by
  rintro hinc
  have := h ▸ hinc.edge_mem
  simp only [mem_empty_iff_false] at this

@[simp]
lemma not_isBetween_of_E_empty (h : G.E = ∅) : ¬ G.IsBetween e x y := by
  contrapose! h
  use e, h.edge_mem

@[simp]
lemma not_adj_of_E_empty (h : G.E = ∅) : ¬ G.Adj x y := by
  rintro ⟨e, hbtw⟩
  exact (h ▸ hbtw.edge_mem : _)

@[simp]
lemma reflAdj_iff_eq_mem_of_E_empty (h : G.E = ∅) : G.reflAdj x y ↔ x = y ∧ x ∈ G.V:= by
  simp only [reflAdj, not_adj_of_E_empty h, false_or]

@[simp]
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

def Edgeless (V : Set α) (β : Type*) : Graph α β where
  V := V
  E := ∅
  incFun := fun _ => 0
  sum_eq := by tauto
  vertex_support := by tauto
  edge_support := by tauto

@[simp]
lemma Edgeless.V (V : Set α) (β : Type*) : (Edgeless V β).V = V := rfl

@[simp]
lemma Edgeless.E (V : Set α) (β : Type*) : (Edgeless V β).E = ∅ := rfl

@[simp]
lemma Edgeless.incFun (V : Set α) (β : Type*) : (Edgeless V β).incFun = 0 := rfl

lemma eq_Edgeless_of_E_empty (h : G.E = ∅) : G = Edgeless G.V β := by
  ext1
  · rfl
  · exact h
  · simp [h]

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

def Isolated (G : Graph α β) (v : α) := ∀ e, ¬ G.Inc e v

namespace Isolated

lemma not_adj_left (hisol : G.Isolated u) : ¬ G.Adj u v := by
  rintro ⟨e, hbtw⟩
  exact hisol e hbtw.inc_left

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
