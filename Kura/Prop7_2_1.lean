import Kura.Operation.Minor2Simp


open Set Function
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

theorem prop721_rec (t : ℕ) [Nonempty α] {G : Graph (Set α) (Sym2 (Set α))}
    [hV : Finite V(G)] [hE : Finite E(G)] [G.SimpleCanonical] (hVnonempty : V(G).Nonempty)
    (hGP : G.IsPartitionGraph) (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  have hEnonempty : E(G).Nonempty := by
    by_contra! hE
    simp only [hE, ncard_empty, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at hcard
    have := hVnonempty.ncard_pos
    omega

  let e := hEnonempty.some
  obtain ⟨x, y, hxy : G.IsLink e x y⟩ := exists_isLink_of_mem_edgeSet hEnonempty.some_mem
  have : E(G / ({e} : Set _) |>.simplify).ncard < E(G).ncard := by
    sorry
    -- rw [← simplify_hasIsom.eq (·.edgeSet.ncard) (·.edgeSet.ncard)]
  simp at this
  have := prop721_rec t (G := G / ({e} : Set _) |>.simplify) (by simpa) ?_
  sorry
  · rw []
    sorry
termination_by E(G).ncard
decreasing_by exact this

theorem prop721 (t : ℕ) [G.Simple] [hV : Finite V(G)] [hE : Finite E(G)] (hVnonempty : V(G).Nonempty)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_type_nonempty
  intro α β hα hβ
  apply forall_setify
  intro G h hS
  revert h
  apply forall_Simplify |₂ (fun {β} G ↦ ∀ [hS : G.Simple], G.IsPartitionGraph → ∀ [hV : Finite ↑V(G)]
    [hE : Finite ↑E(G)], V(G).Nonempty → 2 ^ (t - 1) * V(G).ncard ≤ E(G).ncard → G.HasCliqueMinor t)
  intro G _ _ hGP _ _ hVnonempty hcard
  exact prop721_rec t hVnonempty hGP hcard
