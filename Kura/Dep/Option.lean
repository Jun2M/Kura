import Mathlib.Data.Sym.Sym2


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
      exact (ite_some_none_eq_some.mp hb).1
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


end Option
