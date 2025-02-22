import Mathlib.Data.Sym.Sym2.Order
import Kura.Dep.Embedding
import Kura.Dep.UnpackSingleton
import Mathlib.Data.Sym.Card


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
  id_map := by
    intro α sa
    change Sym2.map id sa = sa
    simp only [id_eq, map_id']
  comp_map := by
    intro α β γ f g sa
    change Sym2.map (g ∘ f) sa = Sym2.map g (Sym2.map f sa)
    rw [Sym2.map_map]

-- lemma FunctorSetLikeCommute {α β : Type u} (f : α → β) :
--   (SetLike.coe ∘ (f <$> ·) : Sym2 α → Set β) = (f <$> ·) ∘ SetLike.coe := by
--   ext s b
--   simp


variable {α : Type*}

lemma out_mk_eq_or_swap (v w : α) : Quot.out s(v, w) = (v, w) ∨ Quot.out s(v, w) = (w, v) := by
  unfold Quot.out
  obtain h := Classical.choose_spec (@Quot.exists_rep (α × α) (Sym2.Rel α) s(v, w))
  simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, or_self] at h ⊢
  exact h

lemma eq_mk_out (x : Sym2 α) : x = s(x.out.1, x.out.2) := (Quot.out_eq _).symm

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


-- lemma map_rangeFactorization {α β : Type*} (f : α ↪ β) (a : Sym2 α) :
--   Sym2.map f.rangeFactorization a = (a.map f).pmap Subtype.mk (fun a ha => by
--     simp_all [mem_map, Set.mem_range]; obtain ⟨y, hy, hyy⟩ := ha; exact ⟨y, hyy⟩) := by
--   simp [Function.Embedding.rangeFactorization_coe]
--   ext ⟨x, hx⟩
--   obtain ⟨x, rfl⟩ := hx
--   constructor
--   · rintro ⟨⟨y, hy⟩, heq⟩
--     obtain ⟨y, rfl⟩ := hy
--     have : a = s(x, y) := by
--       sorry
--     subst a
--     simp only [map_pair_eq, Set.mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq, pmap_pair,
--       mem_iff, Subtype.mk.injEq, true_or]
--   · rintro h
--     simp only [mem_map, Subtype.mk.injEq]
--     simp at h
--     sorry

@[simp]
theorem equivSym_pair_eq {a b : α} : (equivSym α) s(a, b) = ⟨{a, b}, rfl⟩ := rfl

@[simp]
theorem mem_equivSym_iff_mem (s : Sym2 α) (a : α) : a ∈ equivSym α s ↔ a ∈ s := by
  induction' s with x y
  rw [equivSym_pair_eq]
  simp only [Multiset.insert_eq_cons, Sym.mem_mk, Multiset.mem_cons, Multiset.mem_singleton,
    mem_iff]

@[simp]
theorem mem_equivMultiset_iff_mem (s : Sym2 α) (a : α) : a ∈ (equivMultiset α s).val ↔ a ∈ s := by
  simp only [equivMultiset, Sym.val_eq_coe, Sym.mem_coe]
  exact mem_equivSym_iff_mem s a

@[simp]
theorem other'_eq_of_mk_left (u v : α) [DecidableEq α] :
  Sym2.Mem.other' (mem_mk_left u v) = v := by
  rw [← Sym2.congr_right, Sym2.other_spec']

@[simp]
theorem other'_eq_of_mk_right (u v : α) [DecidableEq α] :
  Sym2.Mem.other' (mem_mk_right u v) = u := by
  rw [← congr_left, eq_swap, Sym2.other_spec']

@[simp]
theorem exist_other'_eq (s : Sym2 α) (u v : α) [DecidableEq α] :
  (∃ (h : u ∈ s), Sym2.Mem.other' h = v) ↔ s = s(u, v) := by
  constructor
  · rintro ⟨ h, rfl ⟩
    exact (other_spec' h).symm
  · rintro rfl
    refine ⟨mem_mk_left u v, by simp⟩


instance instCanLiftSym2Subtype (p : α → Prop) :
  CanLift (Sym2 α) (Sym2 (Subtype p)) (Sym2.map (·.1)) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    rw [Sym2.eq_mk_out x] at h ⊢
    simp_rw [Sym2.mem_iff] at h
    use Sym2.mk (⟨ x.out.1, h x.out.1 (by simp) ⟩, ⟨ x.out.2, h x.out.2 (by simp) ⟩)
    simp

instance instCanLiftSym2CanLift [CanLift α β f p] :
  CanLift (Sym2 α) (Sym2 β) (Sym2.map f) (fun x => ∀ i ∈ x, p i) where
  prf := by
    intro x h
    have : ∀ (x : α), p x → ∃ (y : β), f y = x := CanLift.prf
    obtain ⟨ y1, hy1 ⟩ := this x.out.1 (h x.out.1 (Sym2.out_fst_mem x))
    obtain ⟨ y2, hy2 ⟩ := this x.out.2 (h x.out.2 (Sym2.out_snd_mem x))
    use s(y1, y2)
    simp [hy1, hy2]

noncomputable def liftSym2lift [CanLift α β f p] (x : Sym2 α) (h : ∀ i ∈ x, p i) : Sym2 β := by
  let a : ∃ y, map f y = x := CanLift.prf x h
  choose y _ using a
  exact y


theorem subtype_iff_mem_sat {p : α → Prop} :
  ∀ x : Sym2 α, (∀ y ∈ x, p y) ↔ ∃ x' : Sym2 {x // p x}, x'.map (·.1) = x := by
  intro x
  constructor
  · intro h
    lift x to Sym2 (Subtype p) using h
    use x
  · rintro ⟨ x', hx' ⟩ y hy
    rw [Sym2.eq_mk_out x', Sym2.map_pair_eq] at hx'
    rw [← hx'] at hy
    simp at hy
    rcases hy with rfl | rfl
    exact x'.out.1.2
    exact x'.out.2.2


instance CoeSym2Coercion {β : Type v} [Coe α β] :
  Coe (Sym2 α) (Sym2 β) where
  coe x := x.map (↑)


theorem equivMultisetsymmEq (a b : α):
  (Sym2.equivMultiset α).symm ⟨{a, b}, rfl⟩ = s(a, b) := by
  rfl

private theorem mem_equivMultisetsymm_mem_of_eq (a : α) (m : { s // Multiset.card s = 2 })
    (s : Sym2 α) : s = (Sym2.equivMultiset α).symm m → (a ∈ s ↔ a ∈ m.val) := by
  induction' s with x y
  intro h
  rw [Equiv.eq_symm_apply] at h
  exact h ▸ (mem_equivMultiset_iff_mem s(x, y) a).symm

@[simp]
theorem mem_equivMultisetsymm_mem (a : α) (m : { s // Multiset.card s = 2 }) :
  a ∈ (Sym2.equivMultiset α).symm m ↔ a ∈ m.val := mem_equivMultisetsymm_mem_of_eq a m _ rfl

theorem mem_equivMultiset_mem (a : α) (s : Sym2 α) :
  a ∈ (Sym2.equivMultiset α s).val ↔ a ∈ s := by
  induction' s with x y
  rw [mem_equivMultiset_iff_mem]

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

lemma map_eq_iff {α β : Type*} {f : α → β} (hf : f.Injective) {s : Sym2 α} {a b : α} :
  (s.map f = s(f a, f b)) ↔ s = s(a, b) := by
  induction' s with x y
  simp only [map_pair_eq, Sym2.eq, rel_iff', Prod.mk.injEq, Function.Injective.eq_iff hf,
    Prod.swap_prod_mk]

def toMultiset (s : Sym2 α) : Multiset α := (Sym2.equivMultiset _ s).val

@[simp]
theorem toMultiset_eq {a b : α} : s(a, b).toMultiset = {a, b} := rfl

@[simp]
theorem toMultiset_card (s : Sym2 α) : Multiset.card s.toMultiset = 2 := by simp [toMultiset]

@[simp]
theorem mem_toMultiset_iff (a : α) (s : Sym2 α) : a ∈ s.toMultiset ↔ a ∈ s := by
  rw [toMultiset, mem_equivMultiset_iff_mem]

theorem equivSym_map_comm (f : α → β) (s : Sym2 α) :
  (Sym2.equivSym β) (s.map f) = (Sym2.equivSym _ s).map f := by
  induction' s with x y
  rfl

@[simp]
theorem map_toMultiset [DecidableEq β] (f : α → β) (s : Sym2 α) :
    (s.map f).toMultiset = s.toMultiset.map f := by
  have := equivSym_map_comm f s
  apply_fun (·.val) at this
  exact this

@[simp]
lemma pmap_toMultiset (P : α → Prop) (f : ∀ a, P a → β) (s : Sym2 α) (h : ∀ a ∈ s, P a) :
    (s.pmap f h).toMultiset = s.toMultiset.pmap f (fun a ha => h a ((mem_toMultiset_iff a s).mp ha)) := by
  induction' s with x y
  rfl

lemma sup_mem [LinearOrder α] (s : Sym2 α) : s.sup ∈ s := by
  rw [eq_mk_out s, Sym2.sup_mk, Sym2.mem_iff, sup_eq_left, sup_eq_right]
  exact le_total _ _

lemma inf_mem [LinearOrder α] (s : Sym2 α) : s.inf ∈ s := by
  rw [eq_mk_out s, Sym2.inf_mk, Sym2.mem_iff, inf_eq_left, inf_eq_right]
  exact le_total _ _

def any (s : Sym2 α) (P : α → Prop) : Prop := by
  refine Sym2.rec (fun ab => P ab.1 ∨ P ab.2) ?_ s
  intro (a, b) (c, d) hr
  simp only [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [eq_rec_constant, or_comm]

@[simp]
lemma any_iff {s : Sym2 α} {P : α → Prop} : s.any P ↔ (∃ a ∈ s, P a):= by
  induction' s with x y
  simp only [any, mem_iff, exists_eq_or_imp, exists_eq_left]
  rfl

def all (s : Sym2 α) (P : α → Prop) : Prop := by
  refine Sym2.rec (fun ab => P ab.1 ∧ P ab.2) ?_ s
  intro (a, b) (c, d) hr
  simp only [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [eq_rec_constant, and_comm]

@[simp]
lemma all_iff (s : Sym2 α) (P : α → Prop) : s.all P ↔ (∀ a ∈ s, P a) := by
  induction' s with x y
  simp only [all, mem_iff, forall_eq_or_imp, forall_eq]
  rfl

@[simp]
lemma equivMultiset_eq (a b : α) : (Sym2.equivMultiset α) s(a, b) = ⟨{a, b}, by simp⟩ := rfl

lemma eq_of_mem_isDiag {s : Sym2 α} {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : s.IsDiag) : a = b := by
  induction' s with x y
  simp_all only [mem_iff, isDiag_iff_proj_eq, or_self]

lemma isDiag_iff_out_fst_eq_out_snd (s : Sym2 α) :
    s.IsDiag ↔ s.out.1 = s.out.2 := by
  conv_lhs => rw [s.eq_mk_out]
  exact isDiag_iff_proj_eq _

@[simp]
lemma map_IsDiag_iff (f : α ↪ β) (s : Sym2 α) :
    (s.map f).IsDiag ↔ s.IsDiag := by
  induction' s with x y
  simp only [map_pair_eq, isDiag_iff_proj_eq, EmbeddingLike.apply_eq_iff_eq]

lemma map_mk {α β : Type*} (f : α → β) (p : α × α) : (Sym2.mk p).map f = s(f p.1, f p.2) := rfl

@[simp]
lemma pmap_eq_pmap_of_imp {P Q : α → Prop} {s : Sym2 α} {f : ∀ a, Q a → β} (h : ∀ a, P a → Q a)
    (hP : ∀ a ∈ s, P a) :
    s.pmap f (fun a ha => h a (hP a ha)) = s.pmap (fun a ha => f a (h a ha)) hP := by
  induction' s with x y
  simp only [pmap_pair]

def IsDiag_equiv (α : Type*) : {e : Sym2 α // e.IsDiag} ≃ α where
  toFun e := Sym2.ofIsDiag e e.2
  invFun a := ⟨s(a, a), by simp⟩
  left_inv e := by
    obtain ⟨e, he⟩ := e
    ext1
    exact eq_ofIsDiag e he
  right_inv a := ofIsDiag_pair

lemma IsDiag_card_eq [DecidableEq α] [Fintype α] :
    Fintype.card {e : Sym2 α // e.IsDiag} = Fintype.card α := by
  rw [Fintype.card_eq]
  exact ⟨IsDiag_equiv α⟩

lemma card_not_IsDiag_eq_choose_two [DecidableEq α] [Fintype α] :
    Fintype.card {e : Sym2 α // ¬ e.IsDiag} = (Fintype.card α).choose 2 := by
  simp only [Fintype.card_subtype_compl, IsDiag_card_eq, Fintype.card_fin, Sym2.card]
  rw [Nat.choose_two_right, Nat.choose_two_right, Nat.add_sub_cancel]
  let n := Fintype.card α
  change (n+1) * n / 2 - n = n * (n + 1 - 2) / 2
  apply_fun (· * 2)
  beta_reduce
  rw [Nat.div_mul_cancel, Nat.sub_mul, Nat.div_mul_cancel, mul_comm, ← Nat.mul_sub]
  · convert Nat.factorial_dvd_ascFactorial n 2 using 1
    simp only [Nat.ascFactorial_succ, add_zero, Nat.ascFactorial_zero, mul_one]
  · by_cases hn : n = 0
    · rw [hn]
      simp only [zero_add, Nat.one_le_ofNat, Nat.sub_eq_zero_of_le, mul_zero, dvd_zero]
    · convert Nat.factorial_dvd_ascFactorial (n - 1) 2 using 1
      simp [Nat.ascFactorial_succ, add_zero, Nat.ascFactorial_zero, mul_one, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  · rintro a b h
    simpa only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] using h

-- example {α β : Type*} :
--   α × β ≃ { a : Sym2 (α ⊕ β) // a.toMultiset.countP (Sum.isLeft ·) = 1 } where
--   toFun ab := ⟨s(Sum.inl ab.1, Sum.inr ab.2), by simp [Multiset.countP_eq_zero]⟩
--   invFun a := by
--     obtain ⟨a, ha⟩ := a
--     rw [Multiset.countP_eq_card_filter] at ha
--     exact (by
--     obtain b := Sym.oneEquiv.symm ⟨_, ha⟩
--     apply Sum.getLeft b
--     sorry
--     , by
--     have hacard := a.toMultiset_card
--     rw [← Multiset.filter_add_not (·.isLeft = true) a.toMultiset, Multiset.card_add, ha, add_comm] at hacard
--     simp at hacard
--     obtain b := Sym.oneEquiv.symm ⟨_, hacard⟩
--     apply Sum.getRight b
--     sorry)
--   left_inv := by
--     simp
--     sorry
--   right_inv := by
--     simp
--     sorry



end Sym2
