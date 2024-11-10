import Mathlib.Data.Sym.Sym2
import Kura.Dep.Embedding


namespace Option


def toMultiset {α : Type u} : Option α → Multiset α
  | none => ∅
  | some a => {a}

@[simp]
theorem filter_ite (o : Option α) (p : α → Bool) :
    o.filter p = o.bind fun a => if p a then some a else none := by
  match o with
  | none => rfl
  | some a => rfl

variable {α : Type u} {p : α → Bool} {o : Option α}

theorem isSome_of_isSome_filter (h : isSome (o.filter p)) : isSome o :=
  match o with
  | none => h
  | some _ => rfl

theorem sat_of_isSome_filter (h : isSome (o.filter p)) : p (o.get (isSome_of_isSome_filter h)) :=
  match o with
  | none => by
    rw [(by rfl: Option.filter p none = none)] at h
    simp_all
  | some a => by
    by_cases hp : p a
    on_goal 2 => rw [(by rfl: Option.filter p (some a) = if p a then some a else none)] at h
    all_goals simp_all

theorem isSome_filter_iff : isSome (o.filter p) ↔ ∃ (h : isSome o), p (o.get h) := by
  match o with
  | none => simp only [Option.filter, isSome_none, Bool.false_eq_true, IsEmpty.exists_iff]
  | some a =>
    simp only [filter_ite, some_bind, get_some, isSome_some, exists_const]
    constructor <;> intro h
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      exact (ite_none_right_eq_some.mp hb).1
    · simp_all

theorem get_filter_eq_get_of_isSome (h : isSome (o.filter p)) :
    (o.filter p).get h = o.get (isSome_of_isSome_filter h) := by
  match o with
  | none => rfl
  | some a =>
    obtain ⟨_hsome, hsat⟩ := isSome_filter_iff.mp h
    simp_all

theorem bind_isSome {f : α → Option β} (hbind : isSome (o.bind f)):
    o.isSome := by match o with
  | none => simp only [none_bind, isSome_none, Bool.false_eq_true] at hbind
  | some _ => simp only [isSome_some]

lemma isSome_bind {f : α → Option β} (h : isSome o) : o.bind f = f (o.get h) := by
  nth_rewrite 1 [← Option.some_get h]
  rw [some_bind]

@[simp]
lemma map_eq_none_iff : o.map f = none ↔ o = none := by
  match o with
  | none => simp only [map_none']
  | some a => simp only [map_some', reduceCtorEq]

@[simp]
lemma none_eq_map_iff : none = o.map f ↔ o = none := by
  match o with
  | none => simp only [map_none']
  | some a => simp only [map_some', reduceCtorEq]

@[simp]
lemma map_eq_some_iff : o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := by
  match o with
  | none => simp only [map_none', reduceCtorEq, false_and, exists_false]
  | some a => simp only [map_some', some.injEq, exists_eq_left']

@[simp]
lemma some_eq_map_iff : some b = o.map f ↔ ∃ a, o = some a ∧ f a = b := by
  match o with
  | none => simp only [map_none', reduceCtorEq, false_and, exists_false]
  | some a => simp only [map_some', some.injEq, eq_comm, exists_eq_left']

@[simp]
lemma map_rangeFactorization {α β : Type*} (f : α ↪ β) (a : Option α) :
  Option.map f.rangeFactorization a = (a.map f).pmap Subtype.mk (fun a ha => by
    simp_all [mem_map, Set.mem_range]; obtain ⟨y, _hy, hyy⟩ := ha; exact ⟨y, hyy⟩) := by
  match a with
  | none => rfl
  | some a => rfl

end Option
