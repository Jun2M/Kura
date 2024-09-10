import Kura.Defs

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W]


structure InducedSubgraph (G : Graph V E) where
  rmv : Set V

structure Subgraph (G : Graph V E) extends InducedSubgraph G where
  rme : Set E
  hv : ∀ e, ∀ v ∈ rmv, v ∈ G.inc e → e ∈ rme

structure QuotientGraph (G : Graph V E) extends InducedSubgraph G where
  vmap : ↑rmvᶜ → ↑rmvᶜ
  vmap_idem : ∀ v, vmap^[2] v = vmap v

structure QuotientSubgraph (G : Graph V E) extends Subgraph G, QuotientGraph G where

structure Minor (G : Graph V E) extends QuotientSubgraph G where
  contracted : ↑rmvᶜ → Option rme
  H : ∀ v, vmap v ≠ v → (contracted v).isSome = true
  h : ∀ v, (hsome : (contracted v).isSome) → G.endAt ((contracted v).get hsome) = {v.val, (vmap v).val}
  -- h : ∀ v, (hne : vmap v ≠ v) → (G.endAt (contracted v|>.get <| H v hne).val) = {v.val, (vmap v).val}


def InducedSubgraph.eval {G : Graph V E} (S : InducedSubgraph G) :
  Graph ↑S.rmvᶜ {e // ∀ v ∈ G.inc e, v ∉ S.rmv} where
  inc e := edge.pmap Subtype.mk (G.inc e.1) e.2

def Subgraph.eval {G : Graph V E} (S : Subgraph G) :
  Graph ↑S.rmvᶜ {e // e ∉ S.rme ∧ ∀ v ∈ G.inc e, v ∉ S.rmv} where
  inc e := edge.pmap Subtype.mk (G.inc e.1) e.2.2

def Minor.eval {G : Graph V E} (S : Minor G) [DecidableEq ↑(Set.range S.vmap)] :
  Graph ↑(Set.range S.vmap) {e // e ∉ S.rme ∧ ∀ v ∈ G.inc e, ∃ (H : v ∉ S.rmv), ⟨v, H⟩ ∈ Set.range S.vmap} where
  inc e := edge.pmap Subtype.mk ((edge.pmap Subtype.mk (G.inc e.1) (e.2.2 · · |>.1)).map S.vmap)
    (fun v h => ⟨ v,
    let ⟨u, _, hh⟩ := mem_map S.vmap v _ h
    hh ▸ S.vmap_idem u⟩)

def hasMinor (G : Graph V E) (H : Graph W F): Prop := ∃ (S : Minor G), Nonempty (Isom S.eval H)



end Graph
