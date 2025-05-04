import Kura.Operation.Minor2


open Set Function
variable {α α' α'' β β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

-- Define Simple graph
-- Define simplification


theorem prop7_2_1 (t : ℕ) [hV : Finite G.V] [hE : Finite G.E] (hVnonempty : G.V.Nonempty)
    (hcard : 2^(t - 1) * G.V.ncard ≤ G.E.ncard) : G.HasCliqueMinor t := by
  -- obtain hVempty | hVnonempty := G.V.eq_empty_or_nonempty
  -- · obtain rfl := vxSet_empty_iff_eq_bot.mp hVempty
  --   sorry

  have hVpos : 0 < G.V.ncard := hVnonempty.ncard_pos hV
  have hEpos : 0 < G.E.ncard := lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (by linarith)) hVpos) hcard
  have hEnonmepty : G.E.Nonempty := (natCard_pos hE).mp hEpos ; clear hEpos hVpos

  let e := hEnonmepty.some
  obtain ⟨x, y, hxy : G.Inc₂ e x y⟩ := exists_inc₂_of_mem_edgeSet hEnonmepty.some_mem
