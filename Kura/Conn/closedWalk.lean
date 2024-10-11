import Kura.Conn.Walk

namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E)


structure Closed extends Walk G where
  startFinish : toWalk.start = toWalk.finish

@[ext, simp]
lemma Closed.ext (c1 c2 : G.Closed) : c1.toWalk = c2.toWalk → c1 = c2 := by
  intro h
  cases c1
  cases c2
  simp_all only

structure Cycle extends Closed G where
  vNodup' : toWalk.vertices.tail.Nodup

namespace Cycle

@[ext, simp]
lemma ext (C1 C2 : G.Cycle) : C1.toWalk = C2.toWalk → C1 = C2 := by
  intro h
  rcases C1 with ⟨⟨w, hw⟩, hnodup⟩
  rcases C2 with ⟨⟨w', hw'⟩, hnodup'⟩
  simpa using h

instance instPreorder : Preorder (Cycle G) where
  le := λ c₁ c₂ => c₁.toWalk.length ≤ c₂.toWalk.length
  le_refl := λ c => Nat.le_refl _
  le_trans := λ c₁ c₂ c₃ => Nat.le_trans

instance DecEq [LinearOrder E] : DecidableEq G.Cycle := by
  intro C1 C2
  refine @decidable_of_decidable_of_iff (C1.toWalk = C2.toWalk) (C1 = C2) ?_ ?_
  infer_instance
  rw [Cycle.ext_iff]

instance instFintype [Fintype E] [LinearOrder E] : Fintype (Cycle G) where
  elems := by
    -- exact (Finset.univ : Finset E)
    --   |>.image Walk.nil
    --   |>.image Walk.extensions
    sorry
  complete := sorry

/-- Cycle has some start point by the definition. rotate it. -/
def rotate (C : G.Cycle) (n : ℕ) : G.Cycle := sorry

/-- Pick a vertex, v, in a cycle. Get a walk from v to v along the cycle -/
def cut (C : G.Cycle) (v : V) (hv : v ∈ C.vertices) : G.Walk := sorry

/-- Pick 2 vertices, u & v, in a cycle. Get edge-disjoint paths u to v and v to u -/
def split (C : G.Cycle) (u v : V) (hu : u ∈ C.vertices) (hv : v ∈ C.vertices) : G.Path × G.Path :=
  sorry

def symmDiff (C1 C2 : G.Cycle) : G.Cycle := sorry

end Cycle

-- def IsVertexCycle (v : V) (c : G.Cycle) : Prop :=
--   @Minimal _ {le:=fun c1 c2 => (c1 : G.Cycle).toWalk.length ≤ (c2 : G.Cycle).toWalk.length} (∀ u ∈ G.neighbourhood v, u ∈ ·.vertices) c


structure Tour extends Closed G, Trail G
