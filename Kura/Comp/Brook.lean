import Kura.Comp.Color

open Set Function WList symmDiff

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}

namespace Graph

theorem brooks_theorem (G : Graph α β) [G.Simple] [hV : Finite V(G)] [hE : Finite E(G)]
    
