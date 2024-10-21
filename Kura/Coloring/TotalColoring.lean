import Kura.Coloring.EdgeColoring
-- import Kura.Coloring.Coloring

namespace Graph
open edge Sym2
variable {V E W F : Type*} [LinearOrder V] [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder F]
  [Fintype F] [LinearOrder W] [Fintype W]


structure TotalColoring (G : Graph V E) [Searchable G] where
  c : V ⊕ E → ℕ
  hvv : ∀ u v : V, G.adj u v → c (Sum.inl u) ≠ c (Sum.inl v)
  hve : ∀ (v : V) (e : E), e ∈ G.incEdges v → c (Sum.inl v) ≠ c (Sum.inr e) ∧
  hee : ∀ e e' : E, G.adj e e' → c (Sum.inr e) ≠ c (Sum.inr e')

def TotalChromaticNumber (G : Graph V E) [Searchable G] : ℕ := sorry

lemma one : ∀ G, TotalChromaticNumber G ≥ Δ(G) + 1 := sorry

example : TotalChromaticNumber (CompleteGraph 5) = Δ(CompleteGraph 5) + 1 := sorry

example : TotalChromaticNumber (CompleteGraph 2) = Δ(CompleteGraph 2) + 2 := sorry

example (n : ℕ): TotalChromaticNumber (CompleteGraph n) = Δ(CompleteGraph n) + 1 ∨
  TotalChromaticNumber (CompleteGraph n) = Δ(CompleteGraph n) + 2 := sorry

example : TotalChromaticNumber (Cycle 6) = 3 := sorry

example (n : ℕ) : TotalChromaticNumber (Cycle n) = 3 ↔ 3 ∣ n := sorry

example (n : ℕ) (hn : 3 ∤ n) : TotalChromaticNumber (Cycle n) = 4 := sorry

example (G : Graph V E) [Searchable G] : TotalChromaticNumber G ≤ 2 * Δ(G) + 1 := by
  wlog hconn : G.connected by
    sorry

  if G ≃ᴳ CompleteGraph n then
    color vertices with Δ colors by Brook's thm
    color edges with Δ + 1 colors by Vizing's thm
  else
    example
  sorry
  done

-- Vizing's conjecture
theorem vizingConjecture (G : Graph V E) [Searchable G] : TotalChromaticNumber G ≤ Δ(G) + 2 := sorry

lemma two (G : Graph V E) [Searchable G] : TotalChromaticNumber G ≤ ListChromaticIndex G + 2 := by
  obtain ⟨cv, hcv⟩ := Delta_plus_one_coloring G
  let l : E → List ℕ := λ e => (List.Ioc 0 (ListChromaticIndex G + 2)) \ (cv (G.v1 e)) \ cv (G.v2 e)
  obtain ⟨ce, hce⟩ := ListColoring G l
  sorry

theorem McDiarmid_Reed (G : Graph V E) [Searchable G] (t : ℕ) (ht : t! > Fintype.card V) :
    TotalChromaticNumber G ≤ ChromaticIndex G + t + 1 := by
  wlog h : G.connected ∧ not complete ∧ not an odd cycle by
    sorry

  obtain ⟨ce, hce⟩ : EdgeColoring G (ChromaticIndex G) := sorry
  obtain ⟨cv, hcv⟩ : Coloring G (ChromaticIndex G) := by
    have : (ChromaticIndex G) ≥ Δ(G) := sorry
    sorry

  let bad : ((Fin (ChromaticIndex G)) ≃ (Fin (ChromaticIndex G))) → (v : V) → (A : Finset E) →
    (hA : A.card = t) → (hA' : ∀ e ∈ A, v ∈ G.get e) → Prop := λ σ v A hA hA' =>
    ∀ aᵢ ∈ A, σ (ce (aᵢ)) = cv (G.other v aᵢ)

  have (v : V) → (A : Finset E) → (hA : A.card = t) → (hA' : ∀ e ∈ A, v ∈ G.get e) :
    Fintype.card { σ // bad σ v A hA hA' } = ((ChromaticIndex G) - t)! := sorry

  have : Fintype.card { A // A.card = t ∧ ∃ v, ∀ e ∈ A, v ∈ G.get e} ≤
    Fintype.card V * (Δ(G)).choose t := sorry

  if hCI : ChromaticIndex G = Δ(G) then
    have : ((ChromaticIndex G) - t)! * Fintype.card V * (Δ(G)).choose t < (ChromaticIndex G)! := sorry
  else
    have : ((ChromaticIndex G) - t)! * Fintype.card V * (Δ(G)).choose t < (ChromaticIndex G)! := sorry

  find such edge color permutation where no bad set exists
  let σ be such permutation

  let H : Graph V { e // σ (ce e) = cv (G.v1 e) ∨ σ (ce e) = cv (G.v2 e) } := {inc := λ e => G.inc e.val}
  obtain ⟨cH, hcH⟩ : EdgeColoring H (t+1) := sorry

  let c : V ⊕ E → ℕ := λ ve => match ve with
    | Sum.inl v => cv v
    | Sum.inr e => if h : σ (ce e) = cv (G.v1 e) ∨ σ (ce e) = cv (G.v2 e) then
        cH ⟨e, h⟩
      else
        σ (ce e)



end Graph
