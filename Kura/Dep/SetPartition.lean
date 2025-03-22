import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Finite.Powerset
import Matroid.ForMathlib.SetPartition

open Set Partition

variable {α : Type*} {s x y z : α}

section Rel

variable {s t : Set α} {a b : α} {P : Partition s}

@[simp]
lemma rel_ofRel'_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] (hs : s = {x | r x x}) :
    (ofRel' r hs).Rel = r := by
  simp only [ofRel', rel_congr, rel_ofRel_eq]

end Rel
