import Kura.Graph.Undirected
import Kura.Graph.Searchable

namespace Graph
open edge Sym2
variable {V : Type*} {E : Type*} [LinearOrder V] [LinearOrder E] (G : Graph V E)

structure EdgeColoring (k : ℕ) where
  color : E → Fin k
  edge_color (e : E) : ∀ e' ∈ G.incEE e, color e ≠ color e'

instance loopless_of_exists_edge_coloring [Undirected G] {k : ℕ} (c : EdgeColoring G k) :
    loopless G where
  no_loops e := by
    intro heloop
    have h := c.edge_color e e <| G.loop_mem_incEE _ heloop
    exact h rfl

lemma exists_edge_coloring_of_loopless [Fintype E] [loopless G] :
    ∃ k, Nonempty (EdgeColoring G k) := by
  use Fintype.card E
  use λ e => (Fintype.orderIsoFinOfCardEq E rfl).invFun e
  intro e e' heince'
  simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv, ne_eq,
    EmbeddingLike.apply_eq_iff_eq]
  exact G.ne_of_mem_incEE_of_notLoop e e' heince' (G.no_loops e)

lemma no_edge_coloring_lt_maxDegree [Fintype V] [G.Searchable] [Undirected G]:
    ∀ k < Δ(G), ¬Nonempty (EdgeColoring G k) := by
  rintro k hk ⟨c⟩
  have _ := loopless_of_exists_edge_coloring G c
  obtain ⟨ v, hv ⟩ := G.maxDegreeVerts_nonempty (Nat.not_eq_zero_of_lt hk)
  rw [mem_maxDegreeVerts, ← incEdges_card_eq_degree, incEdges_eq_outEdges] at hv
  sorry

private partial def rungs [Fintype V] [Fintype E] [G.Searchable] [G.Simple] (x : V) (e : E)
  (he : x = G.v1 e ∨ x = G.v2 e) (c : E → Fin (Δ(G) + 1)) (m : V → Fin (Δ(G) + 1))
  (l : List E) (hlnil : l ≠ []) (hl : ∀ e' ∈ l, x = G.v1 e' ∨ x = G.v2 e') : List E :=
  let y0 := G.goFrom he
  let N := G.outEdges x
    |>.sort (· ≤ ·)
    |>.diff l
    |>.filter (λ e' => c e' = m (G.goFrom (hl (l.getLast hlnil) sorry)))
  if h : N = []
  then l
  else rungs x e he c m (l ++ [N.head h]) sorry sorry

partial def Vizing' [Fintype V] [Fintype E] [G.Searchable] [G.Simple] : E → Fin (Δ(G) + 1) := Id.run do
  let mut C : E → Fin (Δ(G) + 1) := λ e => 0
  let El := Finset.univ.sort (· ≤ · : E → E → Prop)
  for e in El do
    let x := G.v1 e
    let y₀ := G.v2 e
    let y := G.neighbors x |>.sort (· ≤ ·) |>.filter (· ≠ y₀)
    let m : V → Finset (Fin (Δ(G) + 1)) := λ v =>
      Finset.univ.filter (λ c => ∀ e ∈ G.outEdges v, C e ≠ c)

    let mut l : List V := [y₀]
    sorry

  return C




end Graph
