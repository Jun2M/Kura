import Kura.Walk.Cycle

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

def acyclic (G : Graph α β) : Prop := ¬ ∃ w : WList α β, G.IsCycle w

lemma path_subsingleton_of_acyclic (hacyc : G.acyclic) {w₁ w₂ : WList α β}
    (h₁ : G.IsPathFrom {x} {y} w₁) (h₂ : G.IsPathFrom {x} {y} w₂) : w₁ = w₂ := by
  
end Graph
