import Mathlib.Data.Sym.Sym2
-- import Mathlib


namespace Sym2

instance Functor : Functor Sym2 where
  map f := Sym2.map f

@[simp]
lemma Functor.eq_map {α β : Type u} (f : α → β) :
  (f <$> ·) = Sym2.map f := by
  rfl

instance LawfulFunctor : LawfulFunctor Sym2 where
  map_const := by
    intro α β
    rfl
    done
  id_map := by
    intro α sa
    change Sym2.map id sa = sa
    simp only [id_eq, map_id']
    done
  comp_map := by
    intro α β γ f g sa
    change Sym2.map (g ∘ f) sa = Sym2.map g (Sym2.map f sa)
    rw [Sym2.map_map]
    done

-- lemma FunctorSetLikeCommute {α β : Type u} (f : α → β) :
--   (SetLike.coe ∘ (f <$> ·) : Sym2 α → Set β) = (f <$> ·) ∘ SetLike.coe := by
--   ext s b
--   simp
--   done


variable {α : Type*}

lemma out_mk_eq_or_swap (v w : α) : Quot.out s(v, w) = (v, w) ∨ Quot.out s(v, w) = (w, v) := by
  unfold Quot.out
  obtain h := Classical.choose_spec (@Quot.exists_rep (α × α) (Sym2.Rel α) s(v, w))
  simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, or_self] at h ⊢
  exact h

lemma eq_mk_out (x : Sym2 α) : x = s(x.out.1, x.out.2) := by
  simp only [Prod.mk.eta, Quot.out_eq]

lemma eq_iff_out_eq_or_out_swap (x : Sym2 α) (v w : α) :
  x = s(v, w) ↔ x.out = (v, w) ∨ x.out = (w, v) := by
  constructor
  · rintro rfl
    exact Sym2.out_mk_eq_or_swap v w
  · rintro (h | h) <;> rw [Sym2.eq_mk_out x, Sym2.eq_iff] <;> simp [h]

-- lemma CanLiftSym2Subtype (p : α → Prop) :
--   ∀ (x : Sym2 α), (∀ i ∈ x, p i) → ∃ y : Sym2 (Subtype p), Sym2.map (fun x ↦ ↑x) y = x := by
--   intro x h
--   rw [Sym2.eq_mk_out x] at h ⊢
--   simp_rw [Sym2.mem_iff] at h
--   use Sym2.mk (⟨ x.out.1, h x.out.1 (by simp) ⟩, ⟨ x.out.2, h x.out.2 (by simp) ⟩)
--   simp
--   done

instance instCanLiftSym2Subtype (p : α → Prop) :
  CanLift (Sym2 α) (Sym2 (Subtype p)) (Sym2.map (·.1)) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    rw [Sym2.eq_mk_out x] at h ⊢
    simp_rw [Sym2.mem_iff] at h
    use Sym2.mk (⟨ x.out.1, h x.out.1 (by simp) ⟩, ⟨ x.out.2, h x.out.2 (by simp) ⟩)
    simp
    done

instance instCanLiftSym2CanLift [CanLift α β f p] :
  CanLift (Sym2 α) (Sym2 β) (Sym2.map f) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    have : ∀ (x : α), p x → ∃ (y : β), f y = x := CanLift.prf
    obtain ⟨ y1, hy1 ⟩ := this x.out.1 (h x.out.1 (Sym2.out_fst_mem x))
    obtain ⟨ y2, hy2 ⟩ := this x.out.2 (h x.out.2 (Sym2.out_snd_mem x))
    use s(y1, y2)
    simp [hy1, hy2]
    done

noncomputable def liftSym2lift [CanLift α β f p] (x : Sym2 α) (h : ∀ i ∈ x, p i) : Sym2 β := by
  let a : ∃ y, map f y = x := CanLift.prf x h
  choose y _ using a
  exact y


theorem subtype_iff_mem_sat {p : α → Prop} :
  ∀ x : Sym2 α, (∀ y ∈ x, p y) ↔ ∃ x' : Sym2 {x // p x}, x'.map (·.1) = x := by
  intro x
  constructor
  · -- 1.
    intro h
    lift x to Sym2 (Subtype p) using h
    use x
    done
  · -- 2.
    rintro ⟨ x', hx' ⟩ y hy
    rw [Sym2.eq_mk_out x', Sym2.map_pair_eq] at hx'
    rw [← hx'] at hy
    simp at hy
    rcases hy with rfl | rfl
    exact x'.out.1.2
    exact x'.out.2.2
    done


instance CoeSym2Coercion {β : Type v} [Coe α β] :
  Coe (Sym2 α) (Sym2 β) where
  coe x := x.map (↑)


theorem equivMultisetsymmEq (a b : α):
  (Sym2.equivMultiset α).symm ⟨{a, b}, rfl⟩ = s(a, b) := by
  rfl

theorem mem_equivMultisetsymm_mem (a : α) (m : { s // Multiset.card s = 2 }) :
  a ∈ (Sym2.equivMultiset α).symm m ↔ a ∈ m.val:= by
  simp
  sorry

theorem mem_equivMultiset_mem (a : α) (m : Sym2 α) :
  a ∈ (Sym2.equivMultiset α m).val ↔ a ∈ m := by
  simp
  sorry

theorem other_eq_right (a b : α) : Mem.other (by simp : a ∈ s(a, b)) = b := by
  have ha : a ∈ s(a, b) := by simp
  obtain this := Sym2.other_spec ha
  rwa [Sym2.congr_right] at this

theorem other_eq_left (a b : α) : Mem.other (by simp : b ∈ s(a, b)) = a := by
  have hb : b ∈ s(a, b) := by simp
  obtain this := Sym2.other_spec hb
  rwa [Sym2.eq_swap, Sym2.congr_left] at this

theorem other'_eq_right [DecidableEq α] (a b : α) : Mem.other' (by simp : a ∈ s(a, b)) = b := by
  have ha : a ∈ s(a, b) := by simp
  obtain this := Sym2.other_spec' ha
  rwa [Sym2.congr_right] at this

theorem other'_eq_left [DecidableEq α] (a b : α) : Mem.other' (by simp : b ∈ s(a, b)) = a := by
  have hb : b ∈ s(a, b) := by simp
  obtain this := Sym2.other_spec' hb
  rwa [Sym2.eq_swap, Sym2.congr_left] at this


def toMultiset (s : Sym2 α) : Multiset α := (Sym2.equivMultiset _ s).val

@[simp]
theorem toMultiset_eq {a b : α} : s(a, b).toMultiset = {a, b} := rfl

@[simp]
theorem toMultiset_card (s : Sym2 α) : Multiset.card s.toMultiset = 2 := by simp [toMultiset]

def Nodup (s : Sym2 α) : Prop := ¬ s.IsDiag

-- theorem

example {α β : Type*} :
  α × β ≃ { a : Sym2 (α ⊕ β) // a.toMultiset.countP (Sum.isLeft ·) = 1 } where
  toFun ab := ⟨s(Sum.inl ab.1, Sum.inr ab.2), by simp [Multiset.countP_eq_zero]⟩
  invFun a := by
    obtain ⟨a, ha⟩ := a
    rw [Multiset.countP_eq_card_filter] at ha
    exact (by
    obtain b := Sym.oneEquiv.symm ⟨_, ha⟩
    apply Sum.getLeft b
    sorry
    , by
    have hacard := a.toMultiset_card
    rw [← Multiset.filter_add_not (·.isLeft = true) a.toMultiset, Multiset.card_add, ha, add_comm] at hacard
    simp at hacard
    obtain b := Sym.oneEquiv.symm ⟨_, hacard⟩
    apply Sum.getRight b
    sorry)
  left_inv := by
    simp
    sorry
  right_inv := by
    simp
    sorry



end Sym2
