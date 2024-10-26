import Mathlib.Logic.Embedding.Set
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic
import Kura.Dep.UnpackSingleton


lemma Set.rangeSplitting_apply' {α β : Type*} (f : α ↪ β) (x : α) :
    Set.rangeSplitting f ⟨f x, Set.mem_range_self x⟩ = x := by
  change Set.rangeSplitting f.toFun (Set.rangeFactorization f.toFun x) = x
  rw [Set.rightInverse_rangeSplitting f.inj' x]

@[simp]
theorem Function.Embedding.coe_refl {α : Type*} : (Function.Embedding.refl α : α → α) = id := rfl

@[simp]
theorem Function.Embedding.coe_trans {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) :
    ⇑(f.trans g) = g ∘ f := rfl

def Function.Embedding.rangeFactorization {α β : Type*} (f : α ↪ β) : α ↪ Set.range f where
  toFun := Set.rangeFactorization f
  inj' := by
    intro x y h
    rw [Subtype.ext_iff, Set.rangeFactorization_coe, Set.rangeFactorization_coe] at h
    exact f.inj' h

@[simp]
theorem Function.Embedding.rangeFactorization_apply {α β : Type*} (f : α ↪ β) (x : α) :
    f.rangeFactorization x = ⟨f x, Set.mem_range_self x⟩ := rfl

@[simp]
theorem Function.Embedding.rangeFactorization_coe {α β : Type*} (f : α ↪ β) (x : α) :
    (f.rangeFactorization x).val = f x := rfl

@[simp]
theorem Function.Embedding.coe_comp_rangeFactorization {α β : Type*} (f : α ↪ β) :
    Subtype.val ∘ f.rangeFactorization = f := rfl

theorem Function.Embedding.rangeFactorization_surj {α β : Type*} (f : α ↪ β) :
    Function.Surjective (f.rangeFactorization) := by
  rintro ⟨b, y, rfl⟩
  exact ⟨y, rfl⟩

noncomputable def Equiv.ofEmbedding {α β : Type*} (f : α ↪ β) : α ≃ Set.range f :=
  Equiv.ofInjective f f.inj'

noncomputable def Function.Embedding.rangeSplitting {α β : Type*} (f : α ↪ β) : Set.range f ↪ α :=
  (Equiv.ofEmbedding f).symm.toEmbedding

@[simp]
lemma Function.Embedding.rangeSplitting_rangeFactorization {α β : Type*} (f : α ↪ β)
    (x : Set.range f) :
    f.rangeFactorization (f.rangeSplitting x) = x := by
  unfold Function.Embedding.rangeSplitting
  have : f.rangeFactorization = (Equiv.ofEmbedding f) := by rfl
  rw [this]
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]

@[simp]
lemma Function.Embedding.rangeFactorization_rangeSplitting {α β : Type*} (f : α ↪ β) (x : α) :
    f.rangeSplitting (f.rangeFactorization x) = x := by
  unfold Function.Embedding.rangeSplitting
  have : f.rangeFactorization = (Equiv.ofEmbedding f) := by rfl
  rw [this]
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]

@[simp]
lemma Function.Embedding.rangeSplitting_apply {α β : Type*} (f : α ↪ β) (x : α) :
    f.rangeSplitting ⟨f x,⟨x,rfl⟩⟩ = x := Function.Embedding.rangeFactorization_rangeSplitting f x

@[simp]
lemma Function.Embedding.rangeSplitting_eq_val {α β : Type*} (f : α ↪ β) (x : _) :
    f (f.rangeSplitting x) = x.val := by
  have := Function.Embedding.rangeSplitting_rangeFactorization f x
  apply_fun Subtype.val at this
  rwa [rangeFactorization_apply] at this

def Set.rangeSplitting' {α β : Type*} [Fintype α] [DecidableEq β] (f : α ↪ β) :
    Set.range f → α :=
  fun b ↦ (Finset.univ.filter (fun a => f a = b)).unpackSingleton (by
    apply le_antisymm
    · by_contra! h
      rw [Finset.one_lt_card_iff] at h
      obtain ⟨a, b, ha, hb, hab⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [← hb] at ha
      exact hab $ f.inj' ha
    · by_contra! h
      simp only [Nat.lt_one_iff, Finset.card_eq_zero] at h
      rw [Finset.filter_eq_empty_iff] at h
      obtain ⟨b, hb⟩ := b
      simp only [Set.mem_range] at hb
      obtain ⟨a, ha⟩ := hb
      specialize h (Finset.mem_univ a)
      exact h ha)

def Function.Embedding.rangeSplitting' {α β : Type*} [Fintype α] [DecidableEq β] (f : α ↪ β) :
    Set.range f ↪ α where
  toFun := Set.rangeSplitting' f
  inj' := by
    intro x y h
    have : Set.rangeSplitting' f x ∈ Finset.univ.filter (fun a => f a = x) := by
      simp only [Set.rangeSplitting', Finset.unpackSingleton, Multiset.unpackSingleton,
        Finset.filter_val, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Sym.apply_oneEquiv_symm_comm _ f]
      simp only [Sym.map_mk]
      sorry
    rw [h] at this
    simp at this
    sorry

@[simp]
lemma Function.Embedding.rangeSplitting'_cancel {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α ↪ β) (x : Set.range f) : f (f.rangeSplitting' x) = x := by
  unfold Function.Embedding.rangeSplitting' Set.rangeSplitting'
  have := Finset.unpackSingleton_mem (Finset.univ.filter (fun a => f a = x)) (by
    apply le_antisymm
    · by_contra! h
      rw [Finset.one_lt_card_iff] at h
      obtain ⟨a, b, ha, hb, hab⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [← hb] at ha
      exact hab $ f.inj' ha
    · by_contra! h
      simp only [Nat.lt_one_iff, Finset.card_eq_zero] at h
      rw [Finset.filter_eq_empty_iff] at h
      obtain ⟨b, hb⟩ := x
      simp only [Set.mem_range] at hb
      obtain ⟨a, ha⟩ := hb
      specialize h (Finset.mem_univ a)
      exact h ha)
  simpa using this


@[simp]
lemma Function.Embedding.rangeSplitting'_eq_rangeSplitting {α β : Type*} [Fintype α] [DecidableEq β]
  (f : α ↪ β) (x : Set.range f) : f.rangeSplitting' x = f.rangeSplitting x := by
  apply_fun f using f.inj'
  simp only [rangeSplitting'_cancel, rangeSplitting_eq_val]
