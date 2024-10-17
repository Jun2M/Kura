import Mathlib.Data.Sym.Sym2.Order
import Kura.Dep.Embedding
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

theorem mem_sat {p : α → Prop} (a b : α) : (∀ x ∈ s(a, b), p x) ↔ p a ∧ p b := by simp

def pmap {P : α → Prop} (f : ∀ a, P a → β) (s : Sym2 α):
  (∀ a ∈ s, P a) → Sym2 β :=
  let g : (p : α × α) → (∀ a ∈ Sym2.mk p, P a) → Sym2 β :=
    fun p H => s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn (motive := fun (x : Sym2 α) => (∀ a ∈ x, P a) → Sym2 β)
    s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : ∀ a ∈ Sym2.mk p, P a := fun a hmem =>
      Hq a ((Sym2.mk_eq_mk_iff.2 hpq) ▸ hmem : a ∈ Sym2.mk q)
    refine (by rintro s₂ rfl _; rfl : ∀ {s₂ e H}, @Eq.ndrec (Sym2 α) (Sym2.mk p)
      (fun s => (∀ a ∈ s, P a) → Sym2 β) _ s₂ e H = _).trans (Quot.sound (?_) : g p Hp = g q Hq)
    rw [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    apply hpq.imp <;> rintro rfl <;> simp

@[simp]
lemma pmap_pair (P : α → Prop) (f : ∀ a, P a → β) (a b : α) (h : P a) (h' : P b) :
    pmap f s(a, b) (by simp only [mem_iff, forall_eq_or_imp, h, forall_eq, h', and_self]) =
    s(f a h, f b h') := by
  simp only [pmap]

@[simp]
lemma mem_pmap_iff {P : α → Prop} (f : ∀ a, P a → β) (x y : α) (h : ∀ a ∈ s(x, y), P a) (b : β) :
  b ∈ s(x, y).pmap f h ↔ ∃ (a : α) (ha : a ∈ s(x, y)), b = f a (h a ha) := by
  rw [pmap_pair _ _ _ _ (h x (by simp only [mem_iff, true_or])) (h y (by simp only [mem_iff, or_true]))]
  simp only [mem_iff]
  constructor
  · rintro (rfl | rfl)
    · use x, Or.inl rfl
    · use y, Or.inr rfl
  · rintro ⟨a, (rfl | rfl), rfl⟩
    exact Or.inl rfl
    exact Or.inr rfl

@[simp]
lemma pmap_subtype_map_val (P : α → Prop) (s : Sym2 α) (h : ∀ a ∈ s, P a) :
    (s.pmap Subtype.mk h).map Subtype.val = s := by
  ext x
  simp only [mem_map, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨y, hy⟩

    sorry
  ·
    sorry

lemma map_rangeFactorization {α β : Type*} (f : α ↪ β) (a : Sym2 α) :
  Sym2.map f.rangeFactorization a = (a.map f).pmap Subtype.mk (fun a ha => by
    simp_all [mem_map, Set.mem_range]; obtain ⟨y, hy, hyy⟩ := ha; exact ⟨y, hyy⟩) := by
  simp [Function.Embedding.rangeFactorization_coe]
  ext ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := hx
  constructor
  · rintro ⟨⟨y, hy⟩, heq⟩
    obtain ⟨y, rfl⟩ := hy
    have : a = s(x, y) := by
      sorry
    subst a
    simp only [map_pair_eq, Set.mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq, pmap_pair,
      mem_iff, Subtype.mk.injEq, true_or]
  · rintro h
    simp only [mem_map, Subtype.mk.injEq]
    simp at h
    sorry

def attachWith (s : Sym2 α) (P : α → Prop) (f : ∀ a ∈ s, P a) :
  Sym2 {a // P a} :=
  pmap Subtype.mk s f

theorem equivSym_eq (a b : α) : (Sym2.equivSym α) s(a, b) = ⟨{a, b}, sorry⟩ := by
  simp [equivSym, sym2EquivSym']
  sorry

theorem mem_equivSym_iff_mem (s : Sym2 α) : ∀ a : α, a ∈ (Sym2.equivSym α s) ↔ a ∈ s := by
  intro a
  constructor
  · intro h
    sorry
  · intro h
    rw [← Sym2.mem_iff_mem, Sym2.Mem] at h
    obtain ⟨b, rfl⟩ := h
    sorry

theorem mem_equivMultiset_iff_mem (s : Sym2 α) : ∀ a : α, a ∈ (Sym2.equivMultiset α s).val ↔ a ∈ s := by
  intro a
  simp
  sorry

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
  · -- 1.
    intro h
    lift x to Sym2 (Subtype p) using h
    use x
  · -- 2.
    rintro ⟨ x', hx' ⟩ y hy
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

@[simp]
theorem mem_toMultiset_iff (a : α) (s : Sym2 α) : a ∈ s.toMultiset ↔ a ∈ s := by
  rw [toMultiset, mem_equivMultiset_iff_mem]

theorem equivSym_map (f : α → β) (s : Sym2 α) :
  (Sym2.equivSym β) (s.map f) = (Sym2.equivSym _ s).map f := by
  simp only [equivSym, sym2EquivSym', Quot.map, Sym.symEquivSym', Equiv.trans_apply,
    Equiv.coe_fn_mk, Sym.map, Multiset.map, Quot.liftOn, Sym.val_eq_coe]
  -- rw [Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk (fun (l : List α) => l.length = 2) (fun s ↦ Multiset.card s = 2) (fun _ => by rfl) (fun _ => by rfl) _]
  sorry

@[simp]
theorem map_toMultiset [DecidableEq β] (f : α → β) (s : Sym2 α) :
    (s.map f).toMultiset = s.toMultiset.map f := by
  have := equivSym_map f s
  apply_fun (·.val) at this
  exact this

@[simp]
lemma pmap_toMultiset (P : α → Prop) (f : ∀ a, P a → β) (s : Sym2 α) (h : ∀ a ∈ s, P a) :
    (s.pmap f h).toMultiset = s.toMultiset.pmap f (fun a ha => h a ((mem_toMultiset_iff a s).mp ha)) := by
  simp [toMultiset, equivSym_map]
  sorry

def Nodup (s : Sym2 α) : Prop := ¬ s.IsDiag

lemma sup_mem [LinearOrder α] (s : Sym2 α) : s.sup ∈ s := by
  rw [eq_mk_out s, Sym2.sup_mk, Sym2.mem_iff, sup_eq_left, sup_eq_right]
  exact le_total _ _

lemma inf_mem [LinearOrder α] (s : Sym2 α) : s.inf ∈ s := by
  rw [eq_mk_out s, Sym2.inf_mk, Sym2.mem_iff, inf_eq_left, inf_eq_right]
  exact le_total _ _

def any (s : Sym2 α) (P : α → Bool) : Bool := by
  refine Sym2.rec (fun ab => P ab.1 || P ab.2) ?_ s
  intro (a, b) (c, d) hr
  simp only [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [eq_rec_constant, Bool.or_comm]

@[simp]
lemma any_iff (s : Sym2 α) (P : α → Bool) : s.any P ↔ (∃ a ∈ s, P a):= by
  sorry

def all (s : Sym2 α) (P : α → Bool) : Bool := by
  refine Sym2.rec (fun ab => P ab.1 && P ab.2) ?_ s
  intro (a, b) (c, d) hr
  simp only [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [eq_rec_constant, Bool.and_comm]

@[simp]
lemma all_iff (s : Sym2 α) (P : α → Bool) : s.all P ↔ (∀ a ∈ s, P a) := by
  sorry

@[simp]
lemma equivMultiset_eq (a b : α) : (Sym2.equivMultiset α) s(a, b) = ⟨{a, b}, by simp⟩ := rfl

@[simp]
lemma isDiag_iff_inf_eq_sup [LinearOrder α] (s : Sym2 α) : s.IsDiag ↔ s.inf = s.sup := by
  sorry

@[simp]
lemma inf_sup_eq_self [LinearOrder α] (s : Sym2 α) : s(s.inf, s.sup) = s := by
  sorry



-- theorem

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
