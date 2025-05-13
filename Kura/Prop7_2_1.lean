import Kura.Operation.Minor2Simp


open Set Function
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

theorem prop721_rec (t : ℕ) {G : Graph (Set α) (Sym2 (Set α))} [hV : Finite V(G)] [hE : Finite E(G)]
    [G.SimpleCanonical] (hVnonempty : V(G).Nonempty) (hGP : G.IsPartitionGraph)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  have hEnonempty : E(G).Nonempty := by
    by_contra! hE
    simp only [hE, ncard_empty, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at hcard
    have := hVnonempty.ncard_pos
    omega

  let e := hEnonempty.some
  obtain ⟨x, y, hxy : G.Inc₂ e x y⟩ := exists_inc₂_of_mem_edgeSet hEnonempty.some_mem
  have : E(G / ({e} : Set _) |>.simplify).ncard < E(G).ncard := by
    sorry
    -- rw [← simplify_hasIsom.eq (·.edgeSet.ncard) (·.edgeSet.ncard)]
  simp at this
  have := prop721_rec t (G := G / ({e} : Set _) |>.simplify) (by simpa) ?_
  sorry
  sorry
termination_by E(G).ncard
decreasing_by exact this

theorem prop721' (t : ℕ) {G : Graph (Set α) β} [G.Simple] [hV : Finite V(G)] [hE : Finite E(G)]
    (hVnonempty : V(G).Nonempty) (hGP : G.IsPartitionGraph)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_Simplify (α := Set α) (β := β) (fun {β} G ↦ ∀ [hV : Finite ↑V(G)] [hE : Finite ↑E(G)],
    V(G).Nonempty → G.IsPartitionGraph → 2 ^ (t - 1) * V(G).ncard ≤ E(G).ncard → G.HasCliqueMinor t)
  rintro G _ _ _ hVnonempty hGP hcard
  exact prop721_rec t hVnonempty hGP hcard

theorem prop721 (t : ℕ) [hV : Finite V(G)] [hE : Finite E(G)] [G.Simple] (hVnonempty : V(G).Nonempty)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_setify
  rintro G hGP _ _ _ hVnonempty hcard
  exact prop721' t hVnonempty hGP hcard
