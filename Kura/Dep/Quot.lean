import Mathlib.GroupTheory.Coset.Basic
import Kura.Dep.Finset

open Relation
namespace Quotient
variable {α : Type*} {s r : Setoid α}

noncomputable instance instFintypeNC [Fintype α] : Fintype (Quotient r) := Fintype.ofFinite _

instance instFintype [Fintype α] [DecidableEq (Quotient r)]: Fintype (Quotient r) where
  elems := Finset.univ.image (Quotient.mk r)
  complete x := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_rep x

noncomputable def representatives (r : Setoid α) : Set α :=
  (Set.univ : Set (Quotient r)).image Quotient.out

lemma representatives_pairwise_not_r : (representatives r).Pairwise (¬ r.r · ·) := by
  rintro a ha b hb hab h
  unfold representatives at ha hb
  simp only [Set.image_univ, Set.mem_range] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have := Quotient.sound h
  simp only [out_eq] at this
  subst this
  exact hab rfl

noncomputable def EquivQuotientRepresentatives (r : Setoid α) :
    Equiv (Quotient r) (representatives r) := Equiv.ofBijective
  (fun x ↦ by refine ⟨Quotient.out x, ?_⟩; simp only [representatives, Set.image_univ,
    Set.mem_range, out_inj, exists_eq]) (by
  constructor
  · rintro x y h
    simpa only [Subtype.mk.injEq, out_inj] using h
  · rintro ⟨x, hx⟩
    simp only [Subtype.mk.injEq]
    use Quotient.mk r x
    simp only [representatives, Set.image_univ, Set.mem_range] at hx
    obtain ⟨x', rfl⟩ := hx
    simp only [out_eq])

@[simp]
lemma mkout_idem {r : Setoid α} {a : α} :
    (Quotient.mk r (Quotient.mk r a).out).out = (Quotient.mk r a).out := by
  simp only [out_eq]

lemma card_quotient_le_card_quotient_of_le [Fintype α] [DecidableEq α] (hrs : s.r ≤ r.r) :
    Fintype.card (Quotient r) ≤ Fintype.card (Quotient s) := by
  let f : Quotient r → Quotient s := (Quotient.mk s ·.out)
  apply Fintype.card_le_of_injective f
  rintro x y h
  unfold f at h
  rw [eq (r := s)] at h
  exact out_equiv_out.mp (hrs x.out y.out h)

-- lemma card_submodular [Fintype α] [DecidableEq α] (r s : α → α → Prop) :
--     Fintype.card (Quotient <| EqvGen.setoid r) + Fintype.card (Quotient <| EqvGen.setoid s) ≤
--     Fintype.card (Quotient <| EqvGen.setoid <| r ⊓ s) +
--     Fintype.card (Quotient <| EqvGen.setoid <| r ⊔ s) := by

--   sorry

lemma IsEmpty_iff {α : Type*} (r : Setoid α) : IsEmpty (Quotient r) ↔ IsEmpty α := by
  constructor <;> intro h
  · contrapose! h
    simp_all only [not_isEmpty_iff]
    exact ⟨⟦h.some⟧⟩
  · infer_instance

def idmap {α : Type*} {s r : Setoid α} (hsr : s ≤ r) : Quotient s → Quotient r :=
  fun a ↦ Quotient.map' id hsr a

lemma idmap_surjective {α : Type*} {s r : Setoid α} (hsr : s ≤ r) :
    Function.Surjective (idmap hsr) := by
  intro x
  obtain ⟨y, rfl⟩ := exists_rep x
  use ⟦y⟧
  simp only [idmap, map'_mk'', id_eq]

lemma idmap_injective_iff_eq {α : Type*} {s r : Setoid α} (hsr : s ≤ r) :
    Function.Injective (idmap hsr) ↔ s = r := by
  constructor
  · intro h
    ext a b
    refine ⟨(hsr ·), fun hr ↦ ?_⟩
    obtain hinj := @h ⟦a⟧ ⟦b⟧
    simp only [idmap, map'_mk'', id_eq, eq] at hinj
    exact hinj hr
  · rintro rfl a b hab
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    simp_all only [idmap, map'_mk'', id_eq, eq]

lemma idmap_not_injective_of_lt {α : Type*} {s r : Setoid α} (hrs : s < r) :
    ¬ Function.Injective (idmap hrs.le) := by
  rw [idmap_injective_iff_eq]
  exact ne_of_lt hrs

lemma card_quotient_le_card_quotient_of_ge [Fintype α] [DecidableEq α] (hrs : s ≤ r) :
    Fintype.card (Quotient r) ≤ Fintype.card (Quotient s) :=
  Fintype.card_le_of_surjective (idmap hrs) (idmap_surjective hrs)

lemma card_quotient_lt_card_quotient_of_gt [Fintype α] [DecidableEq α] (hrs : s < r) :
    Fintype.card (Quotient r) < Fintype.card (Quotient s) :=
  Fintype.card_lt_of_surjective_not_injective (idmap hrs.le) (idmap_surjective hrs.le) <|
  idmap_not_injective_of_lt hrs


end Quotient

-- def Setoid.Eq (α : Type*) : Setoid α where
--   r := (· = ·)
--   iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

def Equiv.Quotient_bot {α : Type*} : α ≃ Quotient (⊥ : Setoid α) where
  toFun a := Quotient.mk ⊥ a
  invFun q := Quotient.lift id (fun _ _ h ↦ h) q
  left_inv a := by simp only [Quotient.lift_mk, id_eq]
  right_inv q := by
    induction' q using Quotient.ind with a
    simp only [Quotient.lift_mk, id_eq]

instance SubsingletonQuotientTop {α : Type*} : Subsingleton (Quotient (⊤ : Setoid α)) := by
  constructor
  rintro a b
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  exact Quotient.sound trivial

namespace Quot
variable {α : Type*} (r : α → α → Prop)

noncomputable def eqvGen_eqv : Quot r ≃ Quotient (Relation.EqvGen.setoid r) := by
  refine Equiv.ofBijective ?_ ?_
  · apply Quot.lift (fun x => Quotient.mk (Relation.EqvGen.setoid r) x)
    rintro x y h
    exact Quotient.sound (Relation.EqvGen.rel _ _ h)
  · constructor
    · rintro x y h
      let x' := x.out
      let y' := y.out
      have := Quot.liftBeta (r := r) (Quotient.mk (Relation.EqvGen.setoid r) ·) (by
        intro a b h
        rw [Quotient.eq (r := Relation.EqvGen.setoid r)]
        exact Relation.EqvGen.rel _ _ h) x'
      rw [out_eq] at this
      rw [this] at h; clear this
      have := Quot.liftBeta (r := r) (Quotient.mk (Relation.EqvGen.setoid r) ·) (by
        intro a b h
        rw [Quotient.eq (r := Relation.EqvGen.setoid r)]
        exact Relation.EqvGen.rel _ _ h) y'
      rw [out_eq] at this
      rw [this] at h; clear this
      rw [Quotient.eq (r := Relation.EqvGen.setoid r)] at h
      have := Quot.eqvGen_sound h
      rwa [out_eq, out_eq] at this
    · rintro x
      let x' := x.out (s := Relation.EqvGen.setoid r)
      use Quot.mk r x'
      simp only
      rw [← Quotient.out_eq (s := Relation.EqvGen.setoid r) x,
        Quotient.eq (r := Relation.EqvGen.setoid r)]


noncomputable instance instFintype [Fintype α] [DecidableRel r] : Fintype (Quot r) := by
  apply @Fintype.ofEquiv _ _ (@Quotient.fintype α _ (Relation.EqvGen.setoid r) (Classical.decRel _))
  apply (eqvGen_eqv r).symm

-- lemma card_submodular [Fintype α] [DecidableEq α] (r s : α → α → Prop) :
--     Fintype.card (Quot r) + Fintype.card (Quot s) ≤
--     Fintype.card (Quot (r ⊓ s)) + Fintype.card (Quot (r ⊔ s)) := by
--   sorry
