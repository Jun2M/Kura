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
  vmap_idem : ∀ v, vmap (vmap v) = vmap v

structure QuotientSubgraph (G : Graph V E) extends Subgraph G, QuotientGraph G where

structure Minor (G : Graph V E) extends QuotientSubgraph G where
  contracted : ↑rmvᶜ → Option rme
  cert_exist : ∀ v, vmap v ≠ v → (contracted v).isSome = true
  merge_ends : ∀ v, (hsome : (contracted v).isSome) → G.endAt ((contracted v).get hsome) = {v.val, (vmap v).val}
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

variable (G : Graph V E)

def InducedSubgraph.init : InducedSubgraph G where
  rmv := ∅

def Subgraph.init : Subgraph G where
  rmv := ∅
  rme := ∅
  hv := by simp only [Set.mem_empty_iff_false, imp_false, false_implies, implies_true]

def QuotientGraph.init : QuotientGraph G where
  rmv := ∅
  vmap := id
  vmap_idem := by simp only [id_eq, implies_true]

def QuotientSubgraph.init : QuotientSubgraph G :=
  { rmv := ∅, rme := ∅, hv := by simp, vmap := id, vmap_idem := by simp }

def Minor.init : Minor G := {
  rmv := ∅, rme := ∅, hv := by simp, vmap := id, vmap_idem := by simp,
  contracted := fun _ => none, cert_exist := by simp, merge_ends := by simp }

variable {G : Graph V E}

def InducedSubgraph.vrm (G' : InducedSubgraph G) (v : V) : InducedSubgraph G where
  rmv := insert v G'.rmv

def Subgraph.vrm (G' : Subgraph G) (v : V) : Subgraph G where
  rmv := insert v G'.rmv
  rme := G'.rme ∪ {e | v ∈ G.inc e}
  hv := by
    intro e v' hv' hv'e
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hv' with rfl | h
    · exact Or.inr hv'e
    · exact Or.inl (G'.hv e v' h hv'e)

def Subgraph.erm (G' : Subgraph G) (e : E) : Subgraph G :=
  { rmv := G'.rmv, rme := insert e G'.rme, hv := (by
    intro e' v hv hv'e
    simp at hv
    exact Or.inr (G'.hv e' v hv hv'e))}

set_option pp.proofs true in
def Minor.vrm (G' : Minor G) (v : ↑G'.rmvᶜ) : Minor G where
  rmv := G'.rmv ∪ (·.val) '' (G'.vmap ⁻¹' {v})
  rme := G'.rme ∪ {e | ∃ u ∈ G.inc e, u ∈ (·.val) '' (G'.vmap ⁻¹' {v}) }
  hv := by
    intro e v' hv' hv'e
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hv' with h | h
    · exact Or.inl (G'.hv e v' h hv'e)
    · right
      use v'
  vmap := fun u => by
    obtain ⟨hrmv, hnew⟩ := by simpa using u.prop
    refine ⟨G'.vmap ⟨u, hrmv⟩, ?_⟩
    simp
    exact fun _h => (G'.vmap_idem ⟨u, hrmv⟩).symm ▸ (hnew hrmv)
  vmap_idem := fun ⟨u, hu⟩ => by
    simp at hu
    obtain ⟨hrmv, hnew⟩ := hu
    specialize hnew hrmv
    apply Subtype.eq
    beta_reduce
    conv_rhs => simp



    sorry
  contracted := sorry
    -- fun ⟨u, hu⟩ => by
    -- simp at hu
    -- obtain ⟨hne, hnin⟩ := hu
    -- simp only
    -- let ⟨u', hu'⟩ := G'.vmap ⟨u, hnin⟩
    -- if u' = v
    -- then exact none
    -- else exact G'.contracted ⟨u', hu'⟩ >>= fun ⟨e, he⟩ => some ⟨e, Or.inl he⟩
  cert_exist :=
    sorry
    -- fun ⟨u, hu⟩ hmerge => by simp at hmerge
  merge_ends := by sorry




def hasMinor (G : Graph V E) (H : Graph W F): Prop := ∃ (S : Minor G), Nonempty (Isom S.eval H)



end Graph
