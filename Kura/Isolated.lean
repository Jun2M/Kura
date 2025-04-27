import Kura.Graph

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph




@[simp] lemma reflAdj : (Edgeless U β).reflAdj x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma Connected : (Edgeless U β).Connected x y ↔ x = y ∧ x ∈ U := by simp

@[simp] lemma SetConnected : (Edgeless U β).SetConnected S T ↔ (S ∩ T ∩ U).Nonempty := by
  refine ⟨fun ⟨s, hsS, t, htT, hst⟩ ↦ ?_,
  fun ⟨x, ⟨hxS, hxT⟩, hxU⟩ ↦ ⟨x, hxS, x, hxT, Connected.refl hxU⟩⟩
  · rw [Connected] at hst
    obtain ⟨rfl, hsU⟩ := hst
    use s, ⟨hsS, htT⟩, hsU



@[simp]
lemma bot : Isolated (⊥ : Graph α β) v := by
  intro e hinc
  simp only [bot_V, mem_empty_iff_false, not_false_eq_true, not_inc_of_not_vx_mem] at hinc

@[simp]
lemma edgeless : Isolated (Edgeless U β) v := by
  intro e hinc
  simp only [Edgeless.E, mem_empty_iff_false, not_false_eq_true, not_inc_of_not_edge_mem] at hinc

end Isolated

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
