import Mathlib.Logic.Embedding.Set


def Function.Embedding.rangeFactorization {α β : Type*} (f : α ↪ β) : α ↪ Set.range f where
  toFun := Set.rangeFactorization f
  inj' := by
    intro x y h
    rw [Subtype.ext_iff, Set.rangeFactorization_coe, Set.rangeFactorization_coe] at h
    exact f.inj' h

@[simp]
lemma Function.Embedding.rangeFactorization_apply {α β : Type*} (f : α ↪ β) (x : α) :
    f.rangeFactorization x = ⟨f x, Set.mem_range_self x⟩ := rfl

@[simp]
lemma Function.Embedding.rangeFactorization_coe {α β : Type*} (f : α ↪ β) (x : α) :
    (f.rangeFactorization x).val = f x := rfl

@[simp]
lemma Function.Embedding.coe_comp_rangeFactorization {α β : Type*} (f : α ↪ β) :
    Subtype.val ∘ f.rangeFactorization = f := rfl

lemma Function.Embedding.rangeFactorization_surj {α β : Type*} (f : α ↪ β) :
    Function.Surjective (f.rangeFactorization) := by
  rintro ⟨b, y, rfl⟩
  exact ⟨y, rfl⟩
