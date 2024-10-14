import Kura.Graph.Subgraph


namespace Graph
open edge
variable {V₁ V₂ V₃ V₄ E₁ E₂ E₃ E₄ : Type*}
  [LinearOrder V₁] [LinearOrder V₂] [LinearOrder V₃] [LinearOrder V₄]
  [DecidableEq E₁] [DecidableEq E₂] [DecidableEq E₃] [DecidableEq E₄]
  (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) (G₃ : Graph V₃ E₃)


-- Disjoint union of two graphs
def add : Graph (Lex $ V₁ ⊕ V₂) (E₁ ⊕ E₂) where
  inc := λ e => match e with
    | Sum.inl e₁ => (G₁.inc e₁).map Sum.inl
    | Sum.inr e₂ => (G₂.inc e₂).map Sum.inr

-- Gluing two graphs along a common subgraph
def gluing {H : Graph V₃ E₃} (H₁ : H ⊆ᴳ G₁) (H₂ : H ⊆ᴳ G₂) [Fintype V₃] [Fintype E₃] :
    Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)}
          {e : E₁ ⊕ E₂ // e ∉ (Finset.univ.map H₂.fₑ).image Sum.inr} :=
  @Graph.Es _ _ _ (G₁.add G₂
  |>.Qfp (λ v => match v with
    | Sum.inl v₁ => Sum.inl v₁
    | Sum.inr v₂ => if h : v₂ ∈ Set.range H₂.fᵥ
                    then Sum.inl (H₁.fᵥ (H₂.fᵥ.rangeSplitting' ⟨v₂, h⟩))
                    else Sum.inr v₂)
    (sorry : Function.Involutive _)
    (λ v => by sorry))
    {e | e ∉ (Finset.univ.map H₂.fₑ).image Sum.inr}
    (by infer_instance)


end Graph
