import Kura.Conn.Conn

namespace Graph
open edge
variable {V W U E F E' : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U] (G : Graph V E)


-- Merges to the start of the path
def Mpath (P : G.Path) :
    Graph {v : V // v ∉ P.vertices.tail} {e : E // e ∉ P.edges} where
  inc e := G
    |>.Qs {v : V | v ∈ P.vertices.tail} P.start P.start_not_mem_vertices_tail
    |>.Es {e : E | e ∉ P.edges}
    |>.inc e

-- contraction by a rooted forest?

structure MinorOf (H : Graph W F) where
  fw : W → Option V
  fₑ : E → F
  fₑinj : Function.Injective fₑ
  inc : ∀ e : E, (H.inc (fₑ e)).map fw = (G.inc e).map some
  connPreimage : ∀ (w₁ w₂ : W), fw w₁ = fw w₂ → (fw w₁).isSome → H{(Set.range fₑ)ᶜ}ᴳ.conn w₁ w₂


def MinorOf.refl : G.MinorOf G where
  fw := some
  fₑ := id
  fₑinj _ _ := id
  inc _ := rfl
  connPreimage u v huv _hSome := by
    simp only [Option.some.injEq] at huv
    subst huv
    exact conn.refl _ u

def MinorOf.trans {H : Graph W F} {I : Graph U E'} (M1 : G.MinorOf H) (M2 : H.MinorOf I): G.MinorOf I where
  fw w := Option.bind (M2.fw w) M1.fw
  fₑ := M2.fₑ ∘ M1.fₑ
  fₑinj e e' h := M1.fₑinj (M2.fₑinj h)
  inc e := by
    simp only [Function.comp_apply]
    match I.inc (M2.fₑ (M1.fₑ e)) with
    | dir a =>
      rw [map_dir]
      by_cases h : (a.1.map M2.fw).isSome
      · simp only [Option.isSome_map'] at h

        sorry
      sorry
    | undir s =>
      simp only [map_undir]
      sorry
  connPreimage u v huv hSome := by sorry

noncomputable def MinorOf.OfSubgraph {G : Graph V E} {H : Graph W F} (hGH : G ⊆ᴳ H) :
    G.MinorOf H where
  fw w := by
    by_cases hw : w ∈ Set.range hGH.fᵥ
    · exact some (hGH.fᵥEmb.rangeSplitting ⟨w, hw⟩)
    · exact none
  fₑ := hGH.fₑ
  fₑinj := hGH.fₑinj
  inc e := by
    simp only [Set.mem_range, hGH.inc, ← map_comp]
    congr
    ext u v
    simp only [Set.mem_range, Function.comp_apply, exists_apply_eq_apply, ↓reduceDIte,
      Option.mem_def, Option.some.injEq]
    change hGH.fᵥEmb.rangeSplitting ⟨hGH.fᵥEmb u, _⟩ = v ↔ u = v
    rw [Function.Embedding.rangeSplitting_apply]
  connPreimage u v huv hSome := by
    simp only [Set.mem_range, Option.isSome_dite] at hSome huv
    obtain ⟨w, rfl⟩ := hSome
    simp only [Set.mem_range, exists_apply_eq_apply, ↓reduceDIte, Option.some_eq_dite_none_right,
      Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop] at huv
    obtain ⟨⟨y, rfl⟩, hwy⟩ := huv
    have := hGH.fᵥinj hwy
    subst y
    exact conn.refl (H.Es (Set.range hGH.fₑ)ᶜ) (hGH.fᵥ w)
