import Kura.Graph.Remove
import Kura.Examples.Defs
import Mathlib.Data.Matroid.Dual

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] (G : Graph V E)

def acyclic (G : Graph V E) : Prop := ∀ n, IsEmpty <| TourGraph n ⊆ᴳ G



def IndepMatroidOfFintype [Fintype E] : IndepMatroid E := by
  refine IndepMatroid.ofFinite Set.finite_univ ?_ ?_ ?_ ?_ ?_
  refine (fun A => G{A}ᴳ.acyclic)
  · intro n
    by_contra! h
    simp only [not_isEmpty_iff] at h
    obtain ⟨⟨fv, fe, hcomm⟩, hfᵥinj, hfₑinj⟩ := h
    obtain x := fe 0
    apply IsEmpty.elim' _ x
    simp only [Set.isEmpty_coe_sort]
  · rintro A B hB hsu n
    contrapose! hB
    simp only [not_isEmpty_iff] at hB
    obtain ⟨SubG⟩ := hB
    simp only [acyclic, not_forall, not_isEmpty_iff]
    use n
    refine ⟨?_⟩
    apply SubG.trans
    apply (Es_spanningsubgraph_Es_of_subset _ hsu).toSubgraphOf
  · rintro A B hAIndep hBIndep hAltB
    sorry
  · rintro A hAIndep
    simp only [Set.subset_univ]
  done
