import Kuratowski.Dep.Sym2
import Kuratowski.Dep.NotSure
import Kuratowski.Dep.Option
import Kuratowski.Dep.Ordered


inductive Edge (αᵥ αₑ : Type*) [LinearOrder αᵥ] where
| of : (OrderedLen αᵥ 2) → Edge αᵥ αₑ
| di : (Option αᵥ × Option αᵥ) → Edge αᵥ αₑ

structure MultiGraph (αᵥ αₑ : Type*) [LinearOrder αᵥ] where
  V : Set αᵥ
  inc : αₑ → Option (OrderedLen αᵥ 2)
  range_inc : ∀ (e : αₑ) (he : (inc e).isSome), ↑((inc e).get he) ⊆ V


namespace MultiGraph

variable {αᵥ αₑ : Type*} [DecidableEq αᵥ] [DecidableEq αₑ] (G : MultiGraph αᵥ αₑ)

def removeVertex (v : αᵥ) (_ : v ∈ G.V) :
  MultiGraph αᵥ αₑ where
  V := G.V \ {v}
  inc := λ e => (G.inc e).filter (v ∉ ·)
  range_inc := by
    intro e he w hw
    simp_all only [SetLike.mem_coe, Set.mem_diff, Set.mem_singleton_iff]
    obtain ⟨hsome, hsat⟩ := Option.isSome_filter_iff.mp he
    by_cases h : v ∈ ((G.inc e).get <| Option.isSome_of_isSome_filter he)
    · simp_all
    · rw [Option.get_filter_eq_get_of_isSome] at hw
      refine ⟨G.range_inc e hsome hw, ?_⟩
      rintro rfl
      exact h hw

def removeEdge (G : MultiGraph αᵥ αₑ) (e : αₑ) (_ : e ∈ G.E) :
  MultiGraph αᵥ αₑ where
  V := G.V
  inc := Function.update (G.inc ·) e none
  range_inc := by
    intro e' he' v hv
    simp only [SetLike.mem_coe] at hv
    by_cases h : e' = e
    · subst h
      simp at he'
    · rw [Function.update_noteq h] at he'
      simp only [ne_eq, h, not_false_eq_true, Function.update_noteq] at hv
      exact G.range_inc e' he' hv


def vertexMerge (G : MultiGraph αᵥ αₑ) (v w : αᵥ) (hdistinct : v ≠ w)
  (_ : v ∈ G.V) (_ : w ∈ G.V) :
  MultiGraph αᵥ αₑ where
  V := G.V \ {w}
  inc := λ e =>
    (G.inc e).map (·.map (λ x => if x = w then v else x))

  domain_inc := rfl

  range_inc := by
    intro e hemap x hx
    simp_all only [ne_eq, SetLike.mem_coe, Set.mem_diff, Set.mem_singleton_iff]

    have : Option.isSome (G.inc e) = true := by
      by_contra heNone
      rw [Option.not_isSome_iff_eq_none] at heNone
      simp [heNone] at hemap

    simp only [Option.get_map _ _ _ this, Sym2.mem_map] at hx
    obtain ⟨u , hu, habsurd⟩ := hx
    simp only [ite_eq_iff] at habsurd
    obtain ⟨rfl, rfl⟩ | ⟨_, rfl⟩ := habsurd <;> simp_all
    exact G.range_inc e this hu





end MultiGraphDissociatedNames
