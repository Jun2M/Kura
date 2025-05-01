import Kura.Le

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

section Degree

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, (G.IncFun e v : ℕ∞)

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

def regular (G : Graph α β) := ∃ d, ∀ v, G.degree v = d

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.IncFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_finsum [Finite β] (G : Graph α β) (v : α) :
    G.degree v = ∑ᶠ e, G.IncFun e v := by
  have := Fintype.ofFinite β
  rw [degree_eq_fintype_sum, finsum_eq_sum_of_fintype]

@[simp]
lemma finsum_incFun_eq (he : e ∈ G.E) : ∑ᶠ v, G.IncFun e v = 2 := by
  simp_rw [← IncFun.sum_eq he, Finsupp.sum, id_eq]
  rw [finsum_eq_finset_sum_of_support_subset]
  simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) :
    ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.IncFun e v) G.E.toFinite (Set.finite_univ (α := α))
  convert h.symm using 1
  · simp only [Set.mem_univ, finsum_true, degree_eq_finsum, finsum_mem_def]
    convert rfl with v e
    simp only [Set.indicator_apply_eq_self, incFun_eq_zero, not_imp_not]
    apply Inc.edge_mem
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show G.E = G.E from rfl) (fun x h ↦ finsum_incFun_eq h)]
  simp [mul_comm]

end Degree


section Connected

@[simp]
def reflAdj (G : Graph α β) (x y : α) := G.Adj x y ∨ x = y ∧ x ∈ G.V

lemma reflAdj_iff_adj_or_eq : G.reflAdj x y ↔ G.Adj x y ∨ x = y ∧ x ∈ G.V := Iff.rfl

lemma reflAdj_iff_or : G.reflAdj x y ↔ x ≠ y ∧ G.Adj x y ∨ x = y ∧ x ∈ G.V := by
  rw [reflAdj_iff_adj_or_eq]
  by_cases hxy : x = y
  · simp only [hxy, true_and, ne_eq, not_true_eq_false, false_and, false_or, or_iff_right_iff_imp]
    exact Adj.mem_left
  · simp only [hxy, false_and, or_false, ne_eq, not_false_eq_true, true_and]

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

lemma Inc.reflAdj_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.reflAdj x y := by
  by_cases hxy : x = y
  · subst y
    right
    exact ⟨rfl, hx.vx_mem⟩
  · left
    use e
    rw [inc₂_iff_inc_and_loop]
    use hx, hy, fun h ↦ (hxy h).elim

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
lemma Inc₂.reflAdj (h : G.Inc₂ e x y) : G.reflAdj x y := by
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

lemma reflAdj.of_le (h : G.reflAdj u v) (hle : G ≤ H) : H.reflAdj u v := by
  obtain hadj | ⟨rfl, hu⟩ := h
  · left
    exact hadj.of_le hle
  · right
    simp only [vx_subset_of_le hle hu, and_self]

@[simp]
lemma reflAdj_iff_eq_mem_of_E_empty (h : G.E = ∅) : G.reflAdj x y ↔ x = y ∧ x ∈ G.V:= by
  simp only [reflAdj, not_adj_of_E_empty h, false_or]

@[simp]
lemma Isolated.reflAdj_iff (hisol : G.Isolated u) : G.reflAdj u v ↔ u = v ∧ u ∈ G.V := by
  simp only [reflAdj, not_adj_left hisol, false_or]



def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

@[simp]
lemma Inc₂.connected (h : G.Inc₂ e x y) : G.Connected x y :=
  Relation.TransGen.single h.reflAdj

@[simp]
lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

@[simp]
lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| reflAdj.of_vxMem hx

lemma Inc.connected_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.Connected x y :=
  reflAdj.connected (hx.reflAdj_of_inc hy)

lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  rw [Relation.transGen_swap]
  congr! 1
  ext
  exact reflAdj.comm

@[simp]
lemma Connected.refl (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

@[simp]
lemma Connected.exists_connected (hx : x ∈ G.V) : ∃ y, G.Connected x y := by
  use x, Connected.refl hx

lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
  rwa [Connected.comm]

instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

lemma Connected.trans (hxy : G.Connected x y) (hyz : G.Connected y z) :
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
lemma Connected.refl_iff : G.Connected x x ↔ x ∈ G.V := by
  refine ⟨?_, Connected.refl⟩
  rintro h
  exact h.mem_left

lemma Connected.of_le (h : G.Connected u v) (hle : G ≤ H) : H.Connected u v := by
  induction h with
  | single huv => exact Relation.TransGen.single (huv.of_le hle)
  | tail huv h ih => exact Relation.TransGen.tail ih (h.of_le hle)

class Conn (G : Graph α β) : Prop where
  all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y

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

@[simp]
lemma Isolated.connected_iff (hisol : G.Isolated u) : G.Connected u v ↔ u = v ∧ u ∈ G.V := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | single hradj => rwa [reflAdj_iff hisol] at hradj
    | tail w hconn ih =>
      obtain ⟨rfl, hu⟩ := ih
      rwa [reflAdj_iff hisol] at hconn
  · rintro ⟨rfl, h⟩
    exact connected_self h


open Partition

def ConnectedPartition (G : Graph α β) : Partition (Set α) := Partition.ofRel (G.Connected)

def Component (G : Graph α β) (v : α) := {u | G.Connected v u}

def ComponentSets (G : Graph α β) (V : Set α) := Component G '' V

@[simp]
lemma ConnectedPartition.supp : G.ConnectedPartition.supp = G.V := by
  simp [ConnectedPartition]

@[simp↓] lemma ConnectedPartition.sSup : sSup G.ConnectedPartition.parts = G.V := supp
@[simp↓] lemma ConnectedPartition.sUnion : ⋃₀ G.ConnectedPartition.parts = G.V := supp

@[simp]
lemma ConnectedPartition.parts : G.ConnectedPartition.parts = G.ComponentSets G.V := by
  ext S
  simp only [ConnectedPartition, ofRel_parts, Connected.refl_iff, setOf_mem_eq, mem_image,
    ComponentSets, Component, mem_setOf_eq]

@[simp]
lemma set_spec_connected_comm : {x | G.Connected x y} = {x | G.Connected y x} := by
  simp_rw [Connected.comm]

lemma set_spec_connected_eq_componentSet : {x | G.Connected y x} = G.Component y := rfl

@[simp]
lemma Component.empty : G.Component x = ∅ ↔ x ∉ G.V := by
  constructor
  · intro h hx
    rw [← mem_empty_iff_false, ← h]
    exact Connected.refl hx
  · intro h
    ext y
    simp [Component, h]

@[simp]
lemma Component.subset_V : G.Component x ⊆ G.V := fun _y hy ↦ hy.mem_right

@[simp]
lemma Component.eq (hx : x ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y :=
  (rel_iff_eqv_class_eq_left (Connected.refl hx)).symm

@[simp]
lemma Component.eq' (hy : y ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y := by
  rw [eq_comm, Connected.comm, eq hy]

@[simp]
lemma Component.mem_partition : G.Component x ∈ G.ConnectedPartition ↔ x ∈ G.V := by
  refine mem_ofRel_iff.trans ?_
  simp +contextual only [Connected.refl_iff, set_spec_connected_eq_componentSet, iff_def,
    forall_exists_index, and_imp, eq', eq]
  refine ⟨fun y hy hconn ↦ hconn.mem_left, fun h ↦ ?_⟩
  use x, h, Connected.refl h

@[simp] lemma Component.mem : y ∈ G.Component x ↔ G.Connected x y := by rfl

lemma Component.mem' : y ∈ G.Component x ↔ G.Connected y x := by
  rw [Connected.comm, Component.mem]

-- @[simp] lemma ComponentSet.self_mem : x ∈ G.ComponentSet x ↔ x ∈ G.V := by simp

@[simp]
lemma ComponentSets.mem (hx : x ∈ G.V) :
    G.Component x ∈ G.ComponentSets T ↔ ∃ y ∈ T, G.Connected x y := by
  simp only [ComponentSets, mem_image, hx, Component.eq']
  simp_rw [Connected.comm]

lemma ComponentSets.componentSet (hx : x ∈ G.V) :
    G.ComponentSets (G.Component x) = {G.Component x} := by
  ext S
  simp +contextual only [mem_singleton_iff, iff_def, hx, mem, Component.mem, and_self,
    Connected.exists_connected, implies_true, and_true]
  rintro ⟨y, hy, rfl⟩
  simpa [hx, Connected.comm] using hy

@[simp]
lemma ComponentSets.sUnion_V : ⋃₀ G.ComponentSets G.V = G.V := by
  rw [← ConnectedPartition.parts]
  exact ConnectedPartition.supp

@[simp] lemma ComponentSets.sSup_V : sSup (G.ComponentSets G.V) = G.V := sUnion_V

lemma ConnectedPartition.le (hle : G ≤ H) : G.ConnectedPartition ≤ H.ConnectedPartition := by
  simpa [ConnectedPartition] using fun u v ↦ (Connected.of_le · hle)

@[simp]
lemma ConnectedPartition.Rel : G.ConnectedPartition.Rel = G.Connected := by
  unfold ConnectedPartition
  rw [rel_ofRel_eq]

def SetConnected (G : Graph α β) (S T : Set α) : Prop := ∃ s ∈ S, ∃ t ∈ T, G.Connected s t

namespace SetConnected
variable {G : Graph α β} {S S' T T' U V : Set α}

lemma refl (h : ∃ x ∈ S, x ∈ G.V) : G.SetConnected S S := by
  obtain ⟨x, hxS, hxV⟩ := h
  use x, hxS, x, hxS, Connected.refl hxV

lemma symm (h : G.SetConnected S T) : G.SetConnected T S := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨t, ht, s, hs, h.symm⟩

lemma comm : G.SetConnected S T ↔ G.SetConnected T S := ⟨SetConnected.symm, SetConnected.symm⟩

lemma left_subset (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hS hs, t, ht

lemma right_subset (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
  rw [SetConnected.comm] at h ⊢
  exact h.left_subset hT

lemma subset (h : G.SetConnected S T) (hS : S ⊆ S') (hT : T ⊆ T') : G.SetConnected S' T' :=
  (h.left_subset hS).right_subset hT

lemma left_supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) T := by
  constructor
  · rintro ⟨s, hsS, t, htT, h⟩
    use s, ⟨hsS, h.mem_left⟩, t, htT
  · rintro ⟨s, ⟨hsS, hs⟩, t, htT, h⟩
    use s, hsS, t, htT

lemma right_supported : G.SetConnected S T ↔ G.SetConnected S (T ∩ G.V) := by
  rw [comm, left_supported, comm]

lemma supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) (T ∩ G.V) := by
  rw [left_supported, right_supported]

lemma of_le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨s, hs, t, ht, h.of_le hle⟩

@[simp]
lemma empty_source : ¬ G.SetConnected ∅ T := by
  rintro ⟨s, hs, t, ht, h⟩
  simp at hs

@[simp]
lemma empty_target : ¬ G.SetConnected S ∅ := by
  rw [SetConnected.comm]
  exact empty_source

@[simp]
lemma nonempty_inter (h : (S ∩ T ∩ G.V).Nonempty) : G.SetConnected S T := by
  obtain ⟨x, ⟨hxS, hxT⟩, hx⟩ := h
  use x, hxS, x, hxT, Connected.refl hx

lemma exists_mem_left (h : G.SetConnected S T) : ∃ x ∈ S, x ∈ G.V := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  exact ⟨s, hs, h.mem_left⟩

lemma exists_mem_right (h : G.SetConnected S T) : ∃ x ∈ T, x ∈ G.V := by
  rw [SetConnected.comm] at h
  exact exists_mem_left h

end SetConnected

namespace Edgeless
@[simp] lemma reflAdj : (Edgeless U β).reflAdj x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma Connected : (Edgeless U β).Connected x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma SetConnected : (Edgeless U β).SetConnected S T ↔ (S ∩ T ∩ U).Nonempty := by
  refine ⟨fun ⟨s, hsS, t, htT, hst⟩ ↦ ?_,
  fun ⟨x, ⟨hxS, hxT⟩, hxU⟩ ↦ ⟨x, hxS, x, hxT, Connected.refl hxU⟩⟩
  · rw [Connected] at hst
    obtain ⟨rfl, hsU⟩ := hst
    use s, ⟨hsS, htT⟩, hsU

end Edgeless

section bot

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

end bot
