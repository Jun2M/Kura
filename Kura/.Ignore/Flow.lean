import Kura.Searchable.Subgraph
import Kura.Dep.CompPoly

namespace Graph
open edge Sym2
variable {V W E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E] (G : Graph V E)
  (u v w : V) (e e' : E)


def steps := {uev : V × E × V // G.canGo uev.1 uev.2.1 uev.2.2}

instance steps.fintype : Fintype G.steps := by
  unfold steps
  infer_instance

instance steps.DecEq : DecidableEq G.steps := by
  unfold steps
  infer_instance

def steps.flip [Undirected G] (uevh : G.steps) : G.steps :=
  let ⟨(u, (e, v)), h⟩ := uevh
  ⟨(v, (e, u)), by rwa [canGo_symm]⟩


structure Circulation (H : Type*) [AddCommGroup H] (G : Graph V E) [Undirected G] where
  f : G.steps → H
  flip : ∀ uev : G.steps, -f uev.flip = f uev
  consv : ∀ v : V, ∑ uevh ∈ Finset.univ.filter fun (uevh : G.steps) => uevh.1.1 ≠ uevh.1.2.2 ∧ v = uevh.1.1, f uevh = 0

namespace Circulation
variable {H : Type*} [AddCommGroup H] {G : Graph V E} [Undirected G]

omit [LinearOrder E] in @[simp]
lemma flip' (C : Circulation H G) (uevh : G.steps) : C.f uevh.flip = -C.f uevh := by
  rw [← neg_neg (C.f _), C.flip]

omit [LinearOrder E] in
theorem ext_iff (C₁ C₂ : Circulation H G) : C₁ = C₂ ↔ ∀ uevh, C₁.f uevh = C₂.f uevh := by
  refine ⟨by rintro rfl _; rfl, fun h => ?_⟩
  rcases C₁ with ⟨f₁, flip₁, consv₁⟩
  rcases C₂ with ⟨f₂, flip₂, consv₂⟩
  simp at h ⊢
  exact funext h

omit [LinearOrder E] in @[ext]
theorem ext (C₁ C₂ : Circulation H G) (h : ∀ uevh, C₁.f uevh = C₂.f uevh) : C₁ = C₂ :=
  (ext_iff C₁ C₂).mpr h

instance : Add (Circulation H G) where
  add := fun C₁ C₂ =>
    { f := fun uevh => C₁.f uevh + C₂.f uevh
    , flip := fun uevh => by
        simp only
        rw [neg_add, C₁.flip, C₂.flip]
    , consv := fun v => by
        rw [Finset.sum_add_distrib]
        simp only [C₁.consv, C₂.consv, add_zero]
    }

omit [LinearOrder E] in @[simp]
theorem add_f (C₁ C₂ : Circulation H G) (uevh : G.steps) :
  (C₁ + C₂).f uevh = C₁.f uevh + C₂.f uevh := rfl

instance : Zero (Circulation H G) where
  zero := { f := fun _ => 0, flip := fun _ => by rw [neg_zero], consv := fun _ => by simp only [edge.canGo.eq_1,
    edge.gofrom?, Finset.sum_const_zero] }

omit [LinearOrder E] in @[simp]
theorem zero : ({ f := fun _ => 0, flip := fun _ => by rw [neg_zero], consv := fun _ => by simp only [edge.canGo.eq_1,
    edge.gofrom?, Finset.sum_const_zero] } : Circulation H G) = 0 := rfl

instance : AddCommGroup (Circulation H G) where
  add_assoc := by
    intros C₁ C₂ C₃
    ext uevh
    change (C₁.f + C₂.f + C₃.f) uevh = (C₁.f + (C₂.f + C₃.f)) uevh
    rw [add_assoc]
  zero_add := by
    intro C
    ext uevh
    change (0 + C.f) uevh = C.f uevh
    rw [zero_add]
  add_zero := by
    intro C
    ext uevh
    change (C.f + 0) uevh = C.f uevh
    rw [add_zero]
  nsmul := fun n C =>
    { f := fun uevh => n • C.f uevh
    , flip := fun uevh => by
        simp only
        rw [← neg_nsmul, C.flip]
    , consv := fun v => by
        rw [Finset.sum_nsmul]
        simp only [C.consv, nsmul_zero]
    }
  nsmul_zero := by
    intro C
    simp only [zero_smul]
    rfl
  nsmul_succ := by
    intro n C
    ext uevh
    simp [add_nsmul]
  neg := fun C =>
    { f := fun uevh => -C.f uevh
    , flip := fun uevh => by
        simp only
        rw [C.flip]
    , consv := fun v => by
        rw [Finset.sum_neg_distrib]
        simp only [C.consv, neg_zero]
    }
  zsmul := fun n C =>
    { f := fun uevh => n • C.f uevh
    , flip := fun uevh => by
        simp only
        rw [← zsmul_neg, C.flip]
    , consv := fun v => by
        rw [Finset.sum_zsmul]
        simp only [C.consv, zsmul_zero]
    }
  zsmul_zero' := by
    intro C
    simp
  zsmul_succ' := by
    intro n C
    ext uevh
    simp [add_zsmul]
  zsmul_neg' := by
    intro n C
    ext uevh
    simp only [negSucc_zsmul, neg_inj, natCast_zsmul]
  neg_add_cancel := by
    intros C
    ext uevh
    change (-C.f + C.f) uevh = 0
    rw [neg_add_cancel]
    rfl
  add_comm := by
    intros C₁ C₂
    ext uevh
    change (C₁.f + C₂.f) uevh = (C₂.f + C₁.f) uevh
    rw [add_comm]

variable (C : Circulation H G) (X Y : Finset V) (v : V)

def F : H :=
  ∑ uevh ∈ Finset.univ.filter
    fun uevh => uevh.1.1 ≠ uevh.1.2.2 ∧ uevh.1.1 ∈ X ∧ uevh.1.2.2 ∈ Y, C.f uevh

omit [LinearOrder E] in
lemma consv' : C.F ({v} : Finset V) Finset.univ = 0 := by
  rw [← C.consv v, F]
  congr
  ext ⟨⟨u, e, w⟩, h⟩
  simp [Eq.comm]

lemma F_add_eq_F_disjUnion (X Y₁ Y₂ : Finset V) (h : Disjoint Y₁ Y₂) :
  C.F X (Y₁.disjUnion Y₂ h) = C.F X Y₁ + C.F X Y₂ := by
  unfold F
  rw [Eq.comm, ← Finset.sum_disjUnion, Finset.disjUnion_eq_union, ← Finset.filter_or]
  congr
  ext ⟨⟨u, e, w⟩, h⟩
  simp
  rw [and_or_left, and_or_left]

  apply Disjoint.of_image_finset (f := λ uevh => uevh.1.2.2)
  sorry
  -- apply Finset.disjoint_of_subset_left

omit [LinearOrder E] in
lemma within_zero :
  C.F X X = 0 := by
  apply Finset.sum_involution (fun uevh _ => steps.flip G uevh) <;>
  rintro ⟨⟨u, e, v⟩, h⟩ hsat <;>
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsat <;>
  obtain ⟨hne, hu, hv⟩ := hsat
  · rw [C.flip', add_neg_cancel]
  · intro _ heq
    rw [steps.flip, ← Subtype.val_inj] at heq
    simp_all only [Prod.mk.injEq, and_false]
  · simp only [steps.flip, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ hne.symm, hv, hu ⟩
  · simp only [steps.flip]

lemma to_all_zero :
  C.F X Finset.univ = 0 := by
  change ∑ uevh ∈ Finset.univ.filter fun uevh => uevh.1.1 ≠ uevh.1.2.2 ∧ uevh.1.1 ∈ X ∧ uevh.1.2.2 ∈ Finset.univ, C.f uevh = 0
  have : (Finset.univ.filter fun uevh => uevh.1.1 ≠ uevh.1.2.2 ∧ uevh.1.1 ∈ X ∧ uevh.1.2.2 ∈ Finset.univ : Finset G.steps) =
    X.disjiUnion (fun v => Finset.univ.filter fun uevh => uevh.1.1 ≠ uevh.1.2.2 ∧ uevh.1.1 ∈ ({v}: Finset V) ∧ uevh.1.2.2 ∈ Finset.univ) (by sorry):= by
    ext ⟨⟨u, e, v⟩, h⟩
    constructor <;>
    · intro hsat
      simp_all

  rw [this, Finset.sum_disjiUnion, Finset.sum_eq_zero]
  intro v hv
  exact C.consv' v

lemma cut_zero (C : Circulation H G) (X : Finset V) :
  C.F X Xᶜ = 0 := by
  have := C.to_all_zero X
  rwa [← Finset.disjUnion_compl_eq_univ X, F_add_eq_F_disjUnion, within_zero, zero_add] at this

end Circulation

structure Flow (H : Type*) [AddCommGroup H] (G : Graph V E) [Undirected G] extends Circulation H G where
  nonneg : ∀ uevh : G.steps, f uevh ≠ 0

theorem nonempty_Z2Flow_iff [Undirected G] : Nonempty (Flow (ZMod 2) G) ↔ ∀ v, Even (G.degree v) := by
  constructor
  · intro ⟨⟨f, hflp, hcsv⟩, h0⟩ v
    have h1 : ∀ uevh : G.steps, f uevh = 1 := (Fin.eq_one_of_neq_zero _ $ h0 ·)
    specialize hcsv v
    simp_rw [h1] at hcsv
    simp at hcsv
    sorry
  · intro h
    refine ⟨⟨fun _ => 1, ?_, ?_⟩, ?_⟩
    · intro uevh
      simp
      rfl
    · intro u
      simp
      specialize h u
      sorry
    · intro ⟨⟨ u, e, v ⟩, h⟩
      simp

-- theorem nonempty_Z3Flow_3reg_iff : Nonempty (Flow (ZMod 3) G) ∧ G.regular 3 ↔ G.IsBipartite := by

def flowPolynomial {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
  (G : Graph V E) [Undirected G] : CompPoly ℤ :=
  if hE : Fintype.card E = 0
  then CompPoly.ofList []
  else
    have hEne : Finset.univ.Nonempty := by
      rwa [Finset.univ_nonempty_iff, ← not_isEmpty_iff, ← Fintype.card_eq_zero_iff.not]
    let e : E := Finset.univ.min' hEne

    let G₁' : Subgraph G := (Subgraph.init G).erm e
    let G₁ := G₁'.eval

    let G₂' : Minor G := (Minor.init G).ctt e (by sorry)
    let G₂ := G₂'.eval

    CompPoly.AddCommGroup.sub (flowPolynomial G₂) (flowPolynomial G₁)
  termination_by (Fintype.card V + Fintype.card E)
  decreasing_by
    · apply Nat.add_lt_add_of_lt_of_le
      · apply Fintype.card_subtype_lt (x := (G.get e).inf) (Minor.inf_not_mem_ctt _ _ _)
      · exact Fintype.card_subtype_le _
    · apply Nat.add_lt_add_of_le_of_lt
      · exact Fintype.card_subtype_le _
      · apply Fintype.card_subtype_lt (x := e)
        exact Subgraph.not_mem_erm _ _ sorry

theorem flowPoly_spec [Undirected G] (H : Type*) [Fintype H] [AddCommGroup H] :
  Nat.card (Flow H G) = (flowPolynomial G).eval ↑(Nat.card H - 1) := by
  induction Fintype.card V using Nat.strongRec with
  | _ _ =>
    rename_i n ih
    by_cases hAllLoops : ∀ e, (G.inc e).isLoop
    · sorry
    · sorry

end Graph
