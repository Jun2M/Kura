import Kura.Connected


open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
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
lemma not_inc₂_of_E_empty (h : G.E = ∅) : ¬ G.Inc₂ e x y := by
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

namespace Edgeless

@[simp] lemma V : (Edgeless U β).V = U := rfl

@[simp] lemma E : (Edgeless U β).E = ∅ := rfl

@[simp] lemma incFun : (Edgeless U β).incFun = 0 := rfl

@[simp] lemma Inc  : ¬ (Edgeless U β).Inc e v  := by simp

@[simp] lemma Inc₂ : ¬ (Edgeless U β).Inc₂ e u v := by simp

@[simp] lemma Adj : ¬ (Edgeless U β).Adj x y := by simp

@[simp] lemma reflAdj : (Edgeless U β).reflAdj x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma Connected : (Edgeless U β).Connected x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma SetConnected : (Edgeless U β).SetConnected S T ↔ (S ∩ T ∩ U).Nonempty := by
  refine ⟨fun ⟨s, hsS, t, htT, hst⟩ ↦ ?_,
  fun ⟨x, ⟨hxS, hxT⟩, hxU⟩ ↦ ⟨x, hxS, x, hxT, Connected.refl hxU⟩⟩
  · rw [Connected] at hst
    obtain ⟨rfl, hsU⟩ := hst
    use s, ⟨hsS, htT⟩, hsU

end Edgeless

@[simp]
lemma edge_empty_iff_eq_Edgeless (G : Graph α β) : G.E = ∅ ↔ G = Edgeless G.V β := by
  constructor
  · rintro h
    ext1
    · rfl
    · exact h
    · ext e v
      simp only [Edgeless.E, mem_empty_iff_false, not_false_eq_true, incFun_of_not_mem_edgeSet,
        Finsupp.coe_zero, Pi.zero_apply, incFun_eq_zero]
      rintro hinc
      have := h ▸ hinc.edge_mem
      simp at this
  · rintro heq
    rw [heq]
    rfl

instance instOrderBotGraph : OrderBot (Graph α β) where
  bot := Edgeless ∅ β
  bot_le G := by refine ⟨?_, ?_, ?_⟩ <;> simp only [Edgeless, empty_subset, mem_empty_iff_false,
    false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥

@[simp] lemma bot_V : (⊥ : Graph α β).V = ∅ := rfl

@[simp] lemma bot_E : (⊥ : Graph α β).E = ∅ := rfl

@[simp] lemma bot_incFun : (⊥ : Graph α β).incFun = 0 := rfl

@[simp]
lemma bot_inc : (⊥ : Graph α β).Inc = fun _ _ ↦ False := by
  ext e a
  simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty]

@[simp]
lemma bot_inc₂ : (⊥ : Graph α β).Inc₂ = fun _ _ _ ↦ False := by
  ext e a b
  simp only [instOrderBotGraph, Edgeless.E, not_inc₂_of_E_empty]

@[simp]
lemma bot_adj : (⊥ : Graph α β).Adj = fun _ _ ↦ False := by
  ext x y
  simp only [instOrderBotGraph, Edgeless.E, not_adj_of_E_empty]

@[simp]
lemma bot_reflAdj : (⊥ : Graph α β).reflAdj = fun _ _ ↦ False := by
  ext x y
  simp

@[simp]
lemma bot_connected : (⊥ : Graph α β).Connected = fun _ _ ↦ False := by
  ext x y
  simp

@[simp]
lemma bot_setConnected : (⊥ : Graph α β).SetConnected = fun _ _ ↦ False := by
  ext S T
  rw [SetConnected.supported]
  simp

@[simp]
lemma vx_empty_iff_eq_bot : G.V = ∅ ↔ G = ⊥ := by
  constructor <;> rintro h
  · apply ext_inc
    · exact h
    · simp only [bot_E]
      by_contra! hE
      have := h ▸ (G.exists_vertex_inc hE.some_mem).choose_spec.vx_mem
      simp only [mem_empty_iff_false] at this
    · simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty, iff_false]
      rintro e v hinc
      have := h ▸ hinc.vx_mem
      simp only [mem_empty_iff_false] at this
  · rw [h]
    rfl

lemma vx_disjoint_of_disjoint (hDisj : Disjoint G H) : Disjoint G.V H.V := by
  intro x hx1 hx2
  let X : Graph α β := Edgeless x β
  specialize hDisj (?_ : X ≤ G) ?_
  · exact ⟨hx1, empty_subset _, by simp [X, Edgeless]⟩
  · exact ⟨hx2, empty_subset _, by simp [X, Edgeless]⟩
  exact hDisj.1

-- Not True!
-- lemma Disjoint.edge_disjoint {G₁ G₂ : Graph α β} (hDisj : Disjoint G₁ G₂) : Disjoint G₁.E G₂.E := by

end edge_empty

section edge_subsingleton

@[simp]
lemma Adj.iff_inc₂_of_E_singleton (h : G.E = {e}) : G.Adj x y ↔ G.Inc₂ e x y := by
  constructor
  · rintro ⟨e, hbtw⟩
    exact (h ▸ hbtw.edge_mem) ▸ hbtw
  · exact fun h => ⟨e, h⟩

@[simp]
lemma Adj.iff_inc₂_of_E_subsingleton (h : G.E ⊆ {e}) : G.Adj x y ↔ G.Inc₂ e x y := by
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
    · rw [reflAdj.Adj_iff_ne hxy, Adj.iff_inc₂_of_E_singleton h] at hradj
      by_cases huy : u = y
      · exact huy ▸ reflAdj.refl ih.mem_left
      · by_cases hux : u = x
        · simp [huy, h, hradj, hux]
        · absurd huy
          rwa [reflAdj.Adj_iff_ne hux, Adj.iff_inc₂_of_E_singleton h, Inc₂.comm,
            hradj.inc₂_iff_eq_right, eq_comm] at ih

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

lemma not_inc₂_left (hisol : G.Isolated u) : ¬ G.Inc₂ e u v :=
  (hisol e ·.inc_left)

lemma not_inc₂_right (hisol : G.Isolated u) : ¬ G.Inc₂ e v u :=
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
