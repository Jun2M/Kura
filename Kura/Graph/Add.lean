-- import Kura.Graph.Remove


-- namespace Graph
-- open edge
-- variable {V₁ V₂ V₃ V₄ E₁ E₂ E₃ E₄ : Type*} {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} {G₃ : Graph V₃ E₃}


-- def Vmap (G₁ : Graph V₁ E₁) (f : V₁ → V₂) : Graph V₂ E₁ where
--   inc e := G₁.inc e |>.map f

-- -- def Isom.OfVEquiv (f : V₁ ≃ V₂) : G₁ ≃ᴳ G₁.Vmap f :=
-- --   Isom.OfEquivs f (Equiv.refl _) (fun e => by simp only [Vmap, Equiv.refl_apply])

-- -- def VImageUnder (f : V₁ → V₂) : Graph (Set.range f) E₁ where
-- --   inc e := G₁.inc e |>.map f
-- --     |>.pmap Subtype.mk (fun v hv => by
-- --       rw [mem_map_iff] at hv
-- --       obtain ⟨u, _hu, rfl⟩ := hv
-- --       exact Set.mem_range_self u)

-- -- noncomputable def EImageUnder (f : E₁ ↪ E₂) : Graph V₁ (Set.range f) where
-- --   inc e := G₁.inc ((Equiv.ofEmbedding f).symm e)


-- def addVertex (G₁ : Graph V₁ E₁) : Graph (WithBot V₁) E₁ := G₁.Vmap some

-- def addVertex_Emb (G₁ : Graph V₁ E₁) : G₁ ⊆ᴳ G₁.addVertex where
--   fᵥ := some
--   fₑ := id
--   inc _ := rfl
--   fᵥinj := Option.some_injective _
--   fₑinj _ _ a := a

-- def addDirEdge (G₁ : Graph V₁ E₁) (A : V₁ × V₁) : Graph V₁ (E₁ ⊕ Unit) where
--   inc := λ e => match e with
--     | Sum.inl e₁ => G₁.inc e₁
--     | Sum.inr _ => dir (A.map some some)

-- def addUndirEdge (G₁ : Graph V₁ E₁) (s : Sym2 V₁) : Graph V₁ (E₁ ⊕ Unit) where
--   inc := λ e => match e with
--     | Sum.inl e₁ => G₁.inc e₁
--     | Sum.inr _ => undir s

-- def addUndirEdge_SpanningEmb (G₁ : Graph V₁ E₁) (s : Sym2 V₁) :
--     G₁.SpanningEmb (G₁.addUndirEdge s) where
--   fᵥ := id
--   fₑ := Sum.inl
--   inc _ := by aesop
--   fᵥinj _ _ a := a
--   fₑinj _ _ a := Sum.inl.inj a
--   fᵥsurj _ := by simp only [id_eq, exists_eq]

-- @[simp]
-- lemma addUndirEdge_inc_inl (G₁ : Graph V₁ E₁) (s : Sym2 V₁) (e : E₁) :
--   (G₁.addUndirEdge s).inc (Sum.inl e) = G₁.inc e := rfl

-- @[simp]
-- lemma addUndirEdge_inc_inr (G₁ : Graph V₁ E₁) (s : Sym2 V₁) :
--   (G₁.addUndirEdge s).inc (Sum.inr ()) = undir s := rfl

-- @[simp]
-- lemma addUndirEdge_SpanningEmb_fᵥ (G₁ : Graph V₁ E₁) (s : Sym2 V₁) :
--     (G₁.addUndirEdge_SpanningEmb s).fᵥ = id := rfl

-- @[simp]
-- lemma addUndirEdge_SpanningEmb_fₑ (G₁ : Graph V₁ E₁) (s : Sym2 V₁) :
--     (G₁.addUndirEdge_SpanningEmb s).fₑ = Sum.inl := rfl

-- def Hom.addUndirEdge (s : Sym2 V₁) (A : Hom G₁ G₂) {e : E₂} (he : G₂.inc e = (undir s).map A.fᵥ) :
--     Hom (G₁.addUndirEdge s) G₂ where
--   fᵥ := A.fᵥ
--   fₑ e' := match e' with
--     | Sum.inl e₁ => A.fₑ e₁
--     | Sum.inr _ => e
--   inc := λ e' => match e' with
--     | Sum.inl e₁ => A.inc e₁
--     | Sum.inr _ => by simp only [he, map_undir, addUndirEdge_inc_inr _ s]

-- @[simp]
-- lemma Hom.addUndirEdge_fᵥ (s : Sym2 V₁) (A : Hom G₁ G₂) {e : E₂}
--     (he : G₂.inc e = (undir s).map A.fᵥ) : (A.addUndirEdge s he).fᵥ = A.fᵥ := rfl

-- @[simp]
-- lemma Hom.addUndirEdge_fₑ (s : Sym2 V₁) (A : Hom G₁ G₂) {e : E₂}
--     (he : G₂.inc e = (undir s).map A.fᵥ) : (A.addUndirEdge s he).fₑ = fun e' => match e' with
--     | Sum.inl e' => A.fₑ e'
--     | Sum.inr _ => e := rfl

-- def Emb.addUndirEdge (s : Sym2 V₁) (A : G₁ ⊆ᴳ G₂) {e : E₂} (heinj : e ∉ Set.range A.fₑ)
--     (he : G₂.inc e = (undir s).map A.fᵥ) : G₁.addUndirEdge s ⊆ᴳ G₂ where
--   toHom := A.toHom.addUndirEdge s he
--   fᵥinj := A.fᵥinj
--   fₑinj e₁ e₂ he₁₂ := by match e₁, e₂ with
--     | Sum.inl e₁, Sum.inl e₂ => simpa [A.fₑinj.eq_iff] using he₁₂
--     | Sum.inl e₁, Sum.inr _ =>
--       simp only [Set.mem_range, not_exists, Hom.addUndirEdge_fₑ] at heinj he₁₂
--       exact (heinj e₁ he₁₂).elim
--     | Sum.inr _, Sum.inl e₂ =>
--       simp only [Set.mem_range, not_exists, Hom.addUndirEdge_fₑ] at heinj he₁₂
--       exact (heinj e₂ he₁₂.symm).elim
--     | Sum.inr _, Sum.inr _ => simp only

-- @[simp]
-- lemma Emb.addUndirEdge_fₑ_inl (s : Sym2 V₁) (A : G₁ ⊆ᴳ G₂) {e : E₂} (e' : E₁)
--     (heinj : e ∉ Set.range A.fₑ) (he : G₂.inc e = (undir s).map A.fᵥ) :
--     (A.addUndirEdge s heinj he).fₑ (Sum.inl e') = A.fₑ e' := by
--   simp only [addUndirEdge, Hom.addUndirEdge_fₑ]

-- @[simp]
-- lemma Emb.addUndirEdge_fₑ_inr (s : Sym2 V₁) (A : G₁ ⊆ᴳ G₂) {e : E₂} (heinj : e ∉ Set.range A.fₑ)
--     (he : G₂.inc e = (undir s).map A.fᵥ) : (A.addUndirEdge s heinj he).fₑ (Sum.inr ()) = e := rfl

-- def addUndirEdge_Emb_iff (s : Sym2 V₁) (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) {e : E₂} :
--     (∃ (A : G₁.addUndirEdge s ⊆ᴳ G₂), A.fₑ (Sum.inr ()) = e) ↔ ∃ (A : G₁ ⊆ᴳ G₂), e ∉ Set.range A.fₑ ∧ G₂.inc e = (undir s).map A.fᵥ := by
--   constructor
--   · rintro ⟨A, rfl⟩
--     refine ⟨⟨⟨A.fᵥ, A.fₑ ∘ Sum.inl, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
--     · rintro e
--       simp only [Function.comp_apply, A.inc, addUndirEdge_inc_inl]
--     · rintro v₁ v₂ hv
--       simpa only [A.fᵥinj.eq_iff] using hv
--     · rintro e₁ e₂ he
--       simpa only [Function.comp_apply, A.fₑinj.eq_iff, Sum.inl.injEq] using he
--     · simp only [Set.mem_range, Function.comp_apply, Emb.fₑinjEq, reduceCtorEq, exists_false,
--       not_false_eq_true]
--     · simp only [A.inc, addUndirEdge_inc_inr, map_undir]
--   · rintro ⟨A, hinj, he⟩
--     refine ⟨A.addUndirEdge s hinj he, ?_⟩
--     simp only [Emb.addUndirEdge_fₑ_inr]

-- instance instAddUndirEdgeUndirected [Undirected G₁] (s : Sym2 V₁) :
--     Undirected (G₁.addUndirEdge s) where
--   all_full e := match e with
--     | Sum.inl e₁ => G₁.all_full e₁
--     | Sum.inr _ => by simp only [isFull, addUndirEdge, inc_eq_undir_v12, undir_isFull]
--   edge_symm e := match e with
--     | Sum.inl e₁ => G₁.edge_symm e₁
--     | Sum.inr _ => by simp only [isUndir, addUndirEdge, inc_eq_undir_v12, isUndir_of_undir]

-- def addApex (vs : Set V₁) : Graph (V₁ ⊕ Unit) (E₁ ⊕ vs) where
--   inc e := match e with
--     | Sum.inl e₁ => (G₁.inc e₁).map Sum.inl
--     | Sum.inr v => undir s(Sum.inr (), Sum.inl v.val)

-- def addApex_Emb (vs : Set V₁) : G₁ ⊆ᴳ G₁.addApex vs where
--   fᵥ := Sum.inl
--   fₑ := Sum.inl
--   inc _ := rfl
--   fᵥinj _ _ a := Sum.inl_injective a
--   fₑinj _ _ a := Sum.inl_injective a

-- @[simp]
-- lemma addApex_Emb_fᵥ (vs : Set V₁) : (G₁.addApex_Emb vs).fᵥ = Sum.inl := rfl

-- @[simp]
-- lemma addApex_Emb_fₑ (vs : Set V₁) : (G₁.addApex_Emb vs).fₑ = Sum.inl := rfl

-- instance instAddApexUndir [Undirected G₁] {vs : Set V₁} :
--     Undirected (G₁.addApex vs) where
--   all_full e := match e with
--     | Sum.inl e₁ => by simp only [isFull, addApex, inc_eq_undir_v12, map_undir, Sym2.map_pair_eq,
--       undir_isFull]
--     | Sum.inr v => by simp only [isFull, addApex, inc_eq_undir_v12, undir_isFull]
--   edge_symm e := match e with
--     | Sum.inl e₁ => by simp only [isUndir, addApex, inc_eq_undir_v12, map_undir, Sym2.map_pair_eq,
--       isUndir_of_undir]
--     | Sum.inr v => by simp only [isUndir, addApex, inc_eq_undir_v12, isUndir_of_undir]


-- def lineGraph [G₁.Undirected] [LinearOrder E₁]:
--     Graph E₁ {e : Sym2 E₁ // ∃ v : V₁, v ∈ (G₁.inc e.inf) ∧ v ∈ (G₁.inc e.sup)} where
--   inc := λ e' => undir e'.val

-- -- def Merge [DecidableEq V₂] {H : Graph V₃ E₃} (A : H ⊆ᴳ G₁) (B : H ⊆ᴳ G₂) :
-- --     Graph {v : V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range B.fᵥ)}
-- --       {e : E₁ ⊕ E₂ // e ∉ Sum.inr '' (Set.range B.fₑ)} :=
-- --   G₁.add G₂
-- --   |>.Qf (by
-- --     intro v
-- --     match v with
-- --     | Sum.inl v₁ => exact Sum.inl v₁
-- --     | Sum.inr v₂ => exact Sum.inr v₂)


-- -- def MergeOnMultualSubgraph [DecidableEq V₂] {H : Graph V₃ E₃} (H₁ : H ⊆ᴳ G₁) (H₂ : H ⊆ᴳ G₂)
-- --     [Fintype V₃] :
-- --     Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)} (E₁ ⊕ E₂) :=
-- --   G₁.add G₂
-- --   |>.Qfp (λ v => match v with
-- --     | Sum.inl v₁ => Sum.inl v₁
-- --     | Sum.inr v₂ => if h : v₂ ∈ Set.range H₂.fᵥ
-- --                     then Sum.inl (H₁.fᵥ (H₂.fᵥEmb.rangeSplitting' ⟨v₂, h⟩))
-- --                     else Sum.inr v₂)
-- --     (fun v ↦ match h : v with
-- --       | Sum.inl v₁ => rfl
-- --       | Sum.inr v₂ => by
-- --         subst h
-- --         simp only [Set.mem_range, Function.Embedding.rangeSplitting'_eq_rangeSplitting]
-- --         split <;> rename_i A a ha <;> split at ha <;> rename_i hy <;> try simp only [reduceCtorEq] at ha
-- --         · obtain ⟨u, hu, rfl⟩ := hy
-- --           change Sum.inl (H₁.fᵥ (H₂.fᵥEmb.rangeSplitting ⟨H₂.fᵥEmb u, _⟩)) = Sum.inl a at ha
-- --           rw [Function.Embedding.rangeSplitting_apply, Sum.inl.inj_iff] at ha
-- --           subst a
-- --           split <;> rename_i hv
-- --           · change _ = Sum.inl (H₁.fᵥ (H₂.fᵥEmb.rangeSplitting ⟨H₂.fᵥEmb u, _⟩))
-- --             simp only [Function.Embedding.rangeSplitting_apply]
-- --           · simp only [exists_apply_eq_apply, not_true_eq_false] at hv
-- --         · rw [Sum.inr.inj_iff] at ha
-- --           subst a
-- --           rfl)
-- --     (λ v => by
-- --       simp only [Set.mem_range, Function.Embedding.rangeSplitting'_eq_rangeSplitting, Sum.exists,
-- --         Set.mem_image, exists_exists_eq_and, not_exists, ne_eq]
-- --       constructor
-- --       · rintro (⟨v₁, h₁⟩ | ⟨v₂, h₂⟩) x <;> subst v
-- --         on_goal 2 => split_ifs with ha
-- --         all_goals try {simp only [reduceCtorEq, not_false_eq_true]}
-- --         push_neg at ha
-- --         exact Sum.inr_injective.ne (ha _)
-- --       · rintro h
-- --         match v with
-- --         | Sum.inl v₁ => exact Or.inl ⟨v₁, rfl⟩
-- --         | Sum.inr v₂ => exact Or.inr ⟨v₂, by
-- --           split_ifs with ha
-- --           · obtain ⟨a, rfl⟩ := ha
-- --             specialize h a
-- --             simp only [not_true_eq_false] at h
-- --           · rfl⟩)


-- -- -- Gluing two graphs along a common subgraph
-- -- def gluing [DecidableEq V₂] [DecidableEq E₁] [DecidableEq E₂] {H : Graph V₃ E₃} (H₁ : H ⊆ᴳ G₁)
-- --   (H₂ : H ⊆ᴳ G₂) [Fintype V₃] [Fintype E₃] :
-- --     Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)}
-- --           {e : E₁ ⊕ E₂ // e ∉ (Finset.univ.map H₂.fₑEmb).image Sum.inr} :=
-- --   (MergeOnMultualSubgraph G₁ G₂ H₁ H₂).Es {e | e ∉ (Finset.univ.map H₂.fₑEmb).image Sum.inr}

-- -- Clique sum
-- -- def cliqueSum [DecidableEq V₂] [DecidableEq E₁] [DecidableEq E₂] (n : ℕ)
-- --   (H₁ : (CompleteGraph n) ⊆ᴳ G₁) (H₂ : (CompleteGraph n) ⊆ᴳ G₂) :
-- --     Graph {v : Lex $ V₁ ⊕ V₂ // v ∉ Sum.inr '' (Set.range H₂.fᵥ)}
-- --           {e : E₁ ⊕ E₂ // e ∉ ((Finset.univ.map H₂.fₑEmb).image Sum.inr ∪ (Finset.univ.map H₁.fₑEmb).image Sum.inl)} :=
-- --   (MergeOnMultualSubgraph G₁ G₂ H₁ H₂).Es
-- --     {e : E₁ ⊕ E₂ | e ∉ ((Finset.univ.map H₂.fₑEmb).image Sum.inr ∪ (Finset.univ.map H₁.fₑEmb).image Sum.inl)}

-- end Graph
