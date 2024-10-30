import Kura.Graph.Remove
import Kura.Examples.Defs


namespace Graph
open edge
variable {V₁ V₂ V₃ V₄ E₁ E₂ E₃ E₄ : Type*}
  (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) (G₃ : Graph V₃ E₃)


def Vmap (f : V₁ → V₂) : Graph V₂ E₁ where
  inc e := G₁.inc e |>.map f

def Isom.OfVEquiv (f : V₁ ≃ V₂) : G₁ ≃ᴳ G₁.Vmap f :=
  ⟨⟨f.toEmbedding, Function.Embedding.refl E₁, sorry⟩,
    ⟨f.symm.toEmbedding, Function.Embedding.refl E₁, sorry⟩⟩

def VImageUnder (f : V₁ → V₂) : Graph (Set.range f) E₁ where
  inc e := G₁.inc e |>.map f
    |>.pmap Subtype.mk (fun v hv => by
      rw [mem_map_iff] at hv
      obtain ⟨u, _hu, rfl⟩ := hv
      exact Set.mem_range_self u)

noncomputable def EImageUnder (f : E₁ ↪ E₂) : Graph V₁ (Set.range f) where
  inc e := G₁.inc ((Equiv.ofEmbedding f).symm e)


def addVertex : Graph (WithBot V₁) E₁ := G₁.Vmap some

def SubgraphOf.addVertex : G₁ ⊆ᴳ G₁.addVertex :=
  ⟨Function.Embedding.some, Function.Embedding.refl E₁, fun _e ↦ rfl⟩


def addDirEdge (A : V₁ × V₁) : Graph V₁ (Lex $ E₁ ⊕ Unit) where
  inc := λ e => match e with
    | Sum.inl e₁ => G₁.inc e₁
    | Sum.inr _ => dir (A.map some some)

def addUndirEdge (s : Sym2 V₁) : Graph V₁ (Lex $ E₁ ⊕ Unit) where
  inc := λ e => match e with
    | Sum.inl e₁ => G₁.inc e₁
    | Sum.inr _ => undir s

def SubgraphOf.addUndirEdge (s : Sym2 V₁) : G₁ ⊆ᴳ G₁.addUndirEdge s :=
  ⟨Function.Embedding.refl V₁, Function.Embedding.inl, fun _e ↦ by
    delta addUndirEdge Lex
    simp only [Function.Embedding.inl_apply, Function.Embedding.coe_refl, map_id]⟩

@[simp]
lemma SubgraphOf.addUndirEdge_fᵥ (s : Sym2 V₁) :
    ⇑(SubgraphOf.addUndirEdge G₁ s).fᵥ = id := rfl

@[simp]
lemma Subgraphof.addUndirEdge_fₑ (s : Sym2 V₁) :
    ⇑(SubgraphOf.addUndirEdge G₁ s).fₑ = Sum.inl := rfl

instance instAddUndirEdgeUndirected [Undirected G₁] (s : Sym2 V₁) :
    Undirected (G₁.addUndirEdge s) where
  all_full e := match e with
    | Sum.inl e₁ => G₁.all_full e₁
    | Sum.inr _ => by simp only [isFull, addUndirEdge, inc_eq_undir_v12, undir_isFull]
  edge_symm e := match e with
    | Sum.inl e₁ => G₁.edge_symm e₁
    | Sum.inr _ => by simp only [isUndir, addUndirEdge, inc_eq_undir_v12, isUndir_of_undir]


def lineGraph [G₁.Undirected] [LinearOrder E₁]:
    Graph E₁ {e : Sym2 E₁ // ∃ v : V₁, v ∈ (G₁.inc e.inf) ∧ v ∈ (G₁.inc e.sup)} where
  inc := λ e' => undir e'.val


-- Disjoint union of two graphs
def add : Graph (Lex $ V₁ ⊕ V₂) (E₁ ⊕ E₂) where
  inc := λ e => match e with
    | Sum.inl e₁ => (G₁.inc e₁).map Sum.inl
    | Sum.inr e₂ => (G₂.inc e₂).map Sum.inr


def MergeOnMultualSubgraph [DecidableEq V₂] {H : Graph V₃ E₃} (H₁ : H ⊆ᴳ G₁) (H₂ : H ⊆ᴳ G₂) [Fintype V₃] [Fintype E₃] :
    Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)} (E₁ ⊕ E₂) :=
  G₁.add G₂
  |>.Qfp (λ v => match v with
    | Sum.inl v₁ => Sum.inl v₁
    | Sum.inr v₂ => if h : v₂ ∈ Set.range H₂.fᵥ
                    then Sum.inl (H₁.fᵥ (H₂.fᵥ.rangeSplitting' ⟨v₂, h⟩))
                    else Sum.inr v₂)
    (fun v ↦ match h : v with
      | Sum.inl v₁ => rfl
      | Sum.inr v₂ => by
        subst h
        simp only [Set.mem_range, Function.Embedding.rangeSplitting'_eq_rangeSplitting]
        split <;> rename_i A a ha <;> split at ha <;> rename_i hy <;> try simp only [reduceCtorEq] at ha
        · obtain ⟨u, hu, rfl⟩ := hy
          rw [Function.Embedding.rangeSplitting_apply, Sum.inl.inj_iff] at ha
          subst a
          split <;> rename_i hv
          · simp only [Function.Embedding.rangeSplitting_apply]
          · simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, not_true_eq_false] at hv
        · rw [Sum.inr.inj_iff] at ha
          subst a
          rfl)
    (λ v => by
      simp only [Set.mem_range, Function.Embedding.rangeSplitting'_eq_rangeSplitting, Lex.exists,
        Sum.exists, Set.mem_image, exists_exists_eq_and, not_exists, ne_eq]
      constructor
      · rintro (⟨v₁, h₁⟩ | ⟨v₂, h₂⟩) x <;> subst v <;> split <;> try {simp only [reduceCtorEq,
          not_false_eq_true]} <;> rename_i A a ha
        · change Sum.inl v₁ = Sum.inr a at ha
          simp only [reduceCtorEq] at ha
        · change Sum.inr v₂ = Sum.inr a at ha
          rw [Sum.inr.inj_iff] at ha
          subst v₂
          split
          · simp only [reduceCtorEq, not_false_eq_true]
          · rename_i ha
            simp only [not_exists] at ha
            rw [Sum.inr.inj_iff]
            exact ha x
      · rintro h
        match v with
        | Sum.inl v₁ => exact Or.inl ⟨v₁, rfl⟩
        | Sum.inr v₂ => exact Or.inr ⟨v₂, by
          split <;> rename_i A a ha <;> change Sum.inr v₂ = _ at ha
          · simp only [reduceCtorEq] at ha
          · rw [Sum.inr.inj_iff] at ha
            subst v₂
            split
            · rename_i hy
              obtain ⟨u, hu, rfl⟩ := hy
              specialize h u
              simp only [not_true_eq_false] at h
            · rfl⟩)


-- Gluing two graphs along a common subgraph
def gluing [DecidableEq V₂] [DecidableEq E₁] [DecidableEq E₂] {H : Graph V₃ E₃} (H₁ : H ⊆ᴳ G₁)
  (H₂ : H ⊆ᴳ G₂) [Fintype V₃] [Fintype E₃] :
    Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)}
          {e : E₁ ⊕ E₂ // e ∉ (Finset.univ.map H₂.fₑ).image Sum.inr} :=
  (MergeOnMultualSubgraph G₁ G₂ H₁ H₂).Es {e | e ∉ (Finset.univ.map H₂.fₑ).image Sum.inr}


-- Clique sum
def cliqueSum [DecidableEq V₂] [DecidableEq E₁] [DecidableEq E₂] (n : ℕ)
  (H₁ : (CompleteGraph n) ⊆ᴳ G₁) (H₂ : (CompleteGraph n) ⊆ᴳ G₂) :
    Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)}
          {e : E₁ ⊕ E₂ // e ∉ ((Finset.univ.map H₂.fₑ).image Sum.inr ∪ (Finset.univ.map H₁.fₑ).image Sum.inl)} :=
  (MergeOnMultualSubgraph G₁ G₂ H₁ H₂).Es
    {e : E₁ ⊕ E₂ | e ∉ ((Finset.univ.map H₂.fₑ).image Sum.inr ∪ (Finset.univ.map H₁.fₑ).image Sum.inl)}

end Graph
