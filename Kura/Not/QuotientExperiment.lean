import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Basic


-- def GraphCN := Multiset (Sym2 ℕ)

-- def GraphN := Sym2 ℕ → Cardinal

-- def Graphn (n : ℕ) := Multiset (Sym2 (Fin n))

def PrePermQuot (V E : Type*) := Quotient ({
  r := λ a b => ∃ f : E ≃ E, a ∘ f = b
  iseqv := {
    refl := λ a => ⟨Equiv.refl E, rfl⟩
    symm := λ ⟨a, h⟩ => ⟨a.symm, (a.comp_symm_eq _ _).mpr h.symm ⟩
    trans := λ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨ b.trans a, by rw [Equiv.coe_trans, ← hb, ← ha]; rfl⟩}}
  : Setoid (E → Sym2 V))

def SetoidVE (V E : Type*) : Setoid (E → Sym2 V) := {
  r := λ a b => ∃ (fE : E ≃ E) (fV : V ≃ V), a = fun x => (b (fE x)).map fV
  iseqv := {
    refl := λ a => ⟨Equiv.refl E, Equiv.refl V, by
      simp only [Equiv.refl_apply, Sym2.map_id', id_eq]⟩
    symm := λ ⟨fE, fV, h⟩ => ⟨fE.symm, fV.symm, by
      simp only [h, Equiv.apply_symm_apply, Sym2.map_map, Function.comp_apply,
        Equiv.symm_apply_apply, Sym2.map_id', id_eq]⟩
    trans := λ ⟨fE1, fV1, h1⟩ ⟨fE2, fV2, h2⟩ => ⟨fE1.trans fE2, fV2.trans fV1, by
      simp only [h1, h2, Sym2.map_map, Function.comp_apply, Equiv.trans_apply]⟩}}

def Graph (V E : Type*) := Quotient (SetoidVE V E)

def CycleGraph (n : ℕ+) : Graph (Fin n) (Fin n) := Quotient.mk _ (λ x => s(x, x + 1))
def CompleteGraph (V : Type*) : Graph V (Sym2 V) := Quotient.mk _ id
def CompleteBipartiteGraph (V : Type*) (S : Set V) : Graph V (S × (Sᶜ : Set V)) :=
  Quotient.mk _ (λ x => s(x.1, x.2))
-- def PathGraph (V : Type*) [Countable V] : Graph V (Fin (n-1)) := Quotient.mk _ (λ x => s(x, x + 1))

unsafe instance (α : Type*) [Repr α] : Repr (Sym2 α) where
  reprPrec s _ :=
    Std.Format.bracket "{" (Std.Format.joinSep ((Sym2.equivMultiset _ s).1.unquot.map repr) ("," ++ Std.Format.line)) "}"

-- #eval @Quotient.out _ (SetoidVE (Fin 3) (Sym2 (Fin 3))) (CompleteGraph (Fin 3)) s(1, 2)

/-
To be implemented
1. The commuting square of quotienting by permutations of the vertex and edge labels
2. Change of labels
3. Embedding of computable graphs to non-computable graphs and the reverse if V and E are finite
4. Given a proof that exactly one member of Sym2 V satisfies a property, return that element.
-/

/-
1. Does the edge type know the number of edges? (i.e. are all edge names refer to a real edge in the graph?)
2. Does the vertex type know the number of vertices? (i.e. are all vertex names refer to a real vertex in the graph?)
3. Is the graph quotiented by the permutation group of the vertex names?
4. Is the graph quotiented by the permutation group of the edge labels?
5. Is the graph computable? (i.e. finite number of vertices and edges)
-/
