import Kura.Conn.Conn

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E)


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
  fₑ : E ↪ F
  comm : ∀ e : E, (H.inc (fₑ e)).map fw = (G.inc e).map some
  connPreimage : ∀ (w₁ w₂ : W), fw w₁ = fw w₂ → (fw w₁).isSome → H{(Set.range fₑ)ᶜ}ᴳ.conn w₁ w₂


def MinorOf.refl : G.MinorOf G where
  fw := some
  fₑ := Function.Embedding.refl E
  comm _ := rfl
  connPreimage u v huv _hSome := by
    simp only [Option.some.injEq] at huv
    subst huv
    exact conn_refl _ u

noncomputable def MinorOf.OfSubgraph {G : Graph V E} {H : Graph W F} (hGH : G ⊆ᴳ H) :
    G.MinorOf H where
  fw w := by
    by_cases hw : w ∈ Set.range hGH.fᵥ
    · exact some (hGH.fᵥ.rangeSplitting ⟨w, hw⟩)
    · exact none
  fₑ := hGH.fₑ
  comm e := by
    simp only [Set.mem_range, hGH.comm, ← map_comp]
    congr
    ext u v
    simp only [Set.mem_range, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq, exists_eq,
      ↓reduceDIte, Function.Embedding.rangeSplitting_apply, Option.mem_def, Option.some.injEq]
  connPreimage u v huv hSome := by
    simp only [Set.mem_range, Option.isSome_dite] at hSome huv
    obtain ⟨w, rfl⟩ := hSome
    simp only [Set.mem_range, EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte,
      Function.Embedding.rangeSplitting_apply] at huv
    by_cases hv : v ∈ Set.range hGH.fᵥ
    · simp only [hv, ↓reduceDIte, Option.some.injEq] at huv
      subst huv
      simp only [Function.Embedding.rangeSplitting_eq_val, conn_refl]
    · simp only [hv, ↓reduceDIte, reduceCtorEq] at huv
