import Wagner.MultiGraph
import Wagner.NotSure


inductive MultiGraphInd (V : Type*) where
  | empty : MultiGraphInd V
  | addEdge : (Sym2 V) → MultiGraphInd V → MultiGraphInd V

inductive MultiGraphIndNat (n : ℕ) where
  | intro : MultiGraphIndNat n
  | addEdge : MultiGraphIndNat n → (Sym2 (Fin n)) → MultiGraphIndNat n

namespace MultiGraphIndNat

variable {V : Type*} {n : ℕ}

def m (G : MultiGraphIndNat n) : ℕ :=
  match G with
  | intro => 0
  | addEdge G _ => G.m + 1

def addVertex (G : MultiGraphIndNat n) : MultiGraphIndNat (n + 1) :=
  match G with
  | intro => intro
  | addEdge G e => addEdge G.addVertex (e.map (↑))

def toMultiGraph (G : MultiGraphIndNat n) : MultiGraph (Fin n) (Fin G.m) :=
  match G with
  | intro => {inc := (Fin0To (Sym2 (Fin n)))}
  | addEdge G' e => {
      inc := λ i =>
        if h : i.val < G'.m then
          G'.toMultiGraph.inc ⟨i.val, h⟩
        else
          e
    }

end MultiGraphIndNat

-- structure MultiGraphAsList (n : ℕ) where
--   l : List (Sym2 (Fin n))

namespace MultiGraphAsList

variable {n : ℕ}

def m (G : List { p : (Fin n) × (Fin n) // p.1 ≤ p.2}) : ℕ := G.length

def toMultiGraphIndNat (G : List { p : (Fin n) × (Fin n) // p.1 ≤ p.2}) :
  MultiGraphIndNat n :=
  match G with
  | [] => MultiGraphIndNat.intro
  | e :: l => MultiGraphIndNat.addEdge (toMultiGraphIndNat l) (Sym2.mk e)

def removeVertex (G : List { p : (Fin n.succ) × (Fin n.succ) // p.1 ≤ p.2}) :
  List { p : (Fin n) × (Fin n) // p.1 ≤ p.2} := by
  refine G.filterMap (λ ⟨ ⟨ p1, p2 ⟩, h ⟩ =>
    if hnsucc : p2.val ≠ n then
      some (⟨ (⟨ p1.val, ?_⟩, ⟨ p2.val, ?_ ⟩), h ⟩)
    else
      none
  )
  simp only [Fin.le_def] at h
  all_goals omega
  done

end MultiGraphAsList


-- noncomputable def removeVertex (G : MultiGraphIndNat (n + 1)) : MultiGraphIndNat n :=
--   match G with
--   | intro => intro
--   | addEdge G e =>
--     if h : ∃ e' : Sym2 (Fin n),  e = e'.map (↑) then
--       by
--         choose e' _ using h
--         exact G.removeVertex.addEdge e'
--     else
--       G.removeVertex

-- lemma constructs {n : ℕ} (G : MultiGraphIndNat n) :
--   ∃ l : List (Sym2 (Fin n)), G = l.foldl addEdge (addVertex^[n] (intro : MultiGraphIndNat 0)) := by
--   sorry

-- def toMultiGraph (g : MultiGraphInd V) :=
--   match g with
--   | empty => ( {inc := λ _ => s(default, default)} : MultiGraph V (Fin 0))
--   | addEdge e g =>
--   let g' := g.toMultiGraph
--   {
--     inc := λ i => by

--       sorry
--       done
--   }
