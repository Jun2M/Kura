import Kura.Comp.Color

open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph


def IsCycleGraph (G : Graph α β) : Prop := sorry
def IsCompleteGraph (G : Graph α β) : Prop := sorry

theorem brooks_theorem (G : Graph α β) [G.Simple] [hV : Finite V(G)] [hE : Finite E(G)]
    [DecidableRel (G.Adj · ·)] (hG : G.Connected) :
    G.IsCycleGraph ∨ G.IsCompleteGraph ∨ G.ChromaticNumber ≤ Δ(G) := by
  rw [Classical.or_iff_not_imp_left, Classical.or_iff_not_imp_left]
  rintro hC hK

  -- Block decomposition
  -- obtain h2conn | h2nconn := em (G.NConnected 2)

  obtain hnonreg | hreg := (em (G.regular)).symm
  · obtain ⟨v, hv, hvdeg⟩ : ∃ x ∈ V(G), G.degree x < Δ(G) := sorry -- not regular

  sorry
