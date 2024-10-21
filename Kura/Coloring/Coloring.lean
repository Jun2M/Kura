import Kura.Graph.Add
import Kura.Graph.Undirected
import Kura.Graph.Searchable

namespace Graph
open edge Sym2
variable {V W E F : Type*} [LinearOrder V] [Fintype V] [DecidableEq E] {G : Graph V E}
  [Searchable G] [Undirected G] [loopless G] (e : E) (u v w : V)

structure coloring (G : Graph V E) [Undirected G] (n : ℕ) where
  colors : V → Fin n
  spec : ∀ e : E, colors (G.v1 e) ≠ colors (G.v2 e)

instance instNonemptyColoringDecidable [Undirected G] (n : ℕ) :
    Decidable (Nonempty (coloring G n)) :=
  sorry

def chromaticNumber (G : Graph V E) [loopless G] [Undirected G] : ℕ :=
  Nat.find (p := λ n => Nonempty (coloring G n)) (by
    use Fintype.card V
    refine ⟨⟨Fintype.equivFin V, ?_⟩⟩
    intro e
    have := (G.isLoop_iff_v1_eq_v2 e).not.mp (G.no_loops e)
    simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq])

lemma chromaticNumber_le_maxDegree_add_one : chromaticNumber G ≤ Δ(G) + 1 := by
  unfold chromaticNumber
  rw [Nat.find_le_iff]
  refine ⟨Δ(G) + 1, le_refl _, ⟨?_, ?_⟩⟩
  · rintro v
    sorry
  · intro e
    sorry


theorem Mycielski (k : ℕ+) : ∃ (V E : Type) (_ : LinearOrder V) (_ : Fintype V) (_ : DecidableEq E)
    (G : Graph V E) (_ : G.loopless) (_ : G.Undirected),
    chromaticNumber G = k ∧ IsEmpty ((CompleteGraph 3) ⊆ᴳ G) := by
  induction k using PNat.strongInductionOn
  rename_i k ih

  if hk1 : k = 1 then
    use Fin 1, Empty, inferInstance, inferInstance, inferInstance, (EdgelessGraph 1), inferInstance,
      inferInstance
    subst k
    refine ⟨?_, ?_⟩
    · unfold chromaticNumber
      rw [Nat.find_eq_iff]
      refine ⟨?_, ?_⟩
      · use fun v ↦ 0
        simp only [IsEmpty.forall_iff]
      · rintro n hn ⟨c, hc⟩
        simp only [PNat.val_ofNat, Nat.lt_one_iff] at hn
        subst n
        specialize c 0
        exact Fin.elim0 c
    · sorry -- number of vertices of subgraph le
  else
    let k' := k - 1
    have hk' : k' + 1 = k := by
      unfold_let
      sorry
    obtain ⟨V, E, _, _, _, G, _, _, hchrom, hsub⟩ := ih k' (by sorry)
    use WithBot (Lex $ V ⊕ V), (E ⊕ E ⊕ E ⊕ V), inferInstance, sorry, inferInstance
    let G' : Graph (WithBot (Lex $ V ⊕ V)) (E ⊕ E ⊕ E ⊕ V) := {
      inc := fun e => match e with
      | Sum.inl e => (G.inc e).map (some ∘ Sum.inl)
      | Sum.inr (Sum.inl e) => undir s(some (Sum.inl (G.v1 e)), some (Sum.inr (G.v2 e)))
      | Sum.inr (Sum.inr (Sum.inl e)) => undir s(some (Sum.inr (G.v1 e)), some (Sum.inl (G.v2 e)))
      | Sum.inr (Sum.inr (Sum.inr v)) => undir s(none, some (Sum.inr v))}
    have : G'.Undirected := by sorry
    use G', sorry, this
    refine ⟨?_, ?_⟩
    · unfold chromaticNumber
      rw [Nat.find_eq_iff]
      refine ⟨⟨?_⟩, ?_⟩
      · unfold chromaticNumber at hchrom
        rw [Nat.find_eq_iff] at hchrom
        obtain ⟨hcExist, hcMin⟩ := hchrom
        obtain ⟨c, hc⟩ := Classical.choice hcExist; clear hcExist
        use fun v => match v with
          | none => Fin.last k
          | some (Sum.inl v) => (c v).castSucc.cast (by norm_cast)
          | some (Sum.inr v) => (c v).castSucc.cast (by norm_cast)
        rintro e
        have : G'.inc e = undir s(G'.v1 e, G'.v2 e) := by sorry
        match e with
        | Sum.inl e =>
          specialize hc e
          simp only [inc_eq_undir_v12, map_undir, Function.comp_apply, map_pair_eq, undir.injEq,
            Sym2.eq, rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h1, ← h2] <;> simp only <;> contrapose! hc
          · exact (Fin.castSucc_inj.mp (Fin.cast_injective _ hc))
          · exact (Fin.castSucc_inj.mp (Fin.cast_injective _ hc.symm))
        | Sum.inr (Sum.inl e) =>
          specialize hc e
          sorry
        | Sum.inr (Sum.inr (Sum.inl e)) =>
          specialize hc e
          sorry
        | Sum.inr (Sum.inr (Sum.inr v)) =>
          sorry
      · rintro n hn ⟨c, hc⟩

        sorry
    ·
      sorry

end Graph
