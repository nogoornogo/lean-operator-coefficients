import Math.RepresentationTheory.Constructions.TypedMixedSeparatedHom

/-! Exact two-boson and mixed-statistics regression theorems on the constructed quotients. -/
namespace Math.MixedCompletenessExamples
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

section Relations
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {n m : ℕ}
def fp : Fin n → Unit := fun _ => ()
def bp : Fin m → Unit := fun _ => ()
abbrev R := TypedMixedExchangeQuotient.relations
  (V := fun _ : Unit => V) (W := fun _ : Unit => W) (fp (n := n)) (bp (m := m))
def pure (v : Fin n → V) (w : Fin m → W) :=
  TypedMixedExchangeQuotient.pure (fp (n := n)) (bp (m := m))
    (fun i _ => v i) (fun j _ => w j)

theorem boson_exchange (v : Fin n → V) (w : Fin m → W) (e : Equiv.Perm (Fin m)) :
    (R (V := V) (W := W) (n := n) (m := m)).mkQ (pure v (w ∘ e)) =
      (R (V := V) (W := W) (n := n) (m := m)).mkQ (pure v w) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span ⟨.inr (⟨e, rfl⟩, (fun i _ => v i), (fun j _ => w j)), rfl⟩

theorem fermion_exchange (v : Fin n → V) (w : Fin m → W) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign e • (R (V := V) (W := W) (n := n) (m := m)).mkQ (pure (v ∘ e) w) =
      (R (V := V) (W := W) (n := n) (m := m)).mkQ (pure v w) := by
  apply sub_eq_zero.mp
  simp only [Units.smul_def]
  rw [← map_zsmul, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span ⟨.inl (⟨e, rfl⟩, (fun i _ => v i), (fun j _ => w j)), rfl⟩

theorem two_boson_exchange (w : Fin 2 → W) :
    (R (V := V) (W := W) (n := 0) (m := 2)).mkQ
      (pure (fun i : Fin 0 => Fin.elim0 i) (w ∘ Equiv.swap 0 1)) =
    (R (V := V) (W := W) (n := 0) (m := 2)).mkQ
      (pure (fun i : Fin 0 => Fin.elim0 i) w) :=
  boson_exchange _ w _

theorem mixed_fermion_sign (v : Fin 2 → V) (w : Fin 2 → W) :
    -(R (V := V) (W := W) (n := 2) (m := 2)).mkQ (pure (v ∘ Equiv.swap 0 1) w) =
      (R (V := V) (W := W) (n := 2) (m := 2)).mkQ (pure v w) := by
  simpa only [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1),
    Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul] using fermion_exchange v w (Equiv.swap 0 1)

theorem mixed_repeated_fermion_zero (v : V) (w : Fin 2 → W) :
    (R (V := V) (W := W) (n := 2) (m := 2)).mkQ (pure (fun _ => v) w) = 0 := by
  have h := mixed_fermion_sign (fun _ => v) w
  have hh : (2 : ℂ) • (R (V := V) (W := W) (n := 2) (m := 2)).mkQ
      (pure (fun _ => v) w) = 0 := by
    simpa only [two_smul, Function.comp_def, neg_eq_iff_add_eq_zero] using h
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
end Relations

section Inverses
variable {G H : Type*} [Group G] [Group H]
  {L M K N : Type*} [AddCommGroup L] [Module ℂ L] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup K] [Module ℂ K] [AddCommGroup N] [Module ℂ N]
  (a : Representation ℂ G L) (b : Representation ℂ G K)
  (c : Representation ℂ H M) (d : Representation ℂ H N)

abbrev Input (n m : ℕ) := MixedPatternAssembly.familySpace
  (TypedMixedSeparatedHom.fieldF (fun _ : Unit => a) (fun _ : Unit => c))
  (TypedMixedSeparatedHom.fieldB (fun _ : Unit => b) (fun _ : Unit => d))
  (fp (n := n)) (bp (m := m))

abbrev Output (n m : ℕ) := IntertwiningMap
  (TypedMixedSeparatedHom.residual (fun _ : Unit => a) (fun _ : Unit => b)
    (fun _ : Unit => c) (fun _ : Unit => d) (fp (n := n)) (bp (m := m)))
  (trivial ℂ H ℂ)

def e (n m : ℕ) : Input a b c d n m ≃ₗ[ℂ] Output a b c d n m :=
  TypedMixedSeparatedHom.familyEquiv
    (fun _ : Unit => a) (fun _ : Unit => b) (fun _ : Unit => c) (fun _ : Unit => d)
    (fp (n := n)) (bp (m := m))

attribute [local irreducible] e

theorem two_boson_reconstruct {n m : ℕ} (hn : n = 0) (hm : m = 2)
    (f : Input a b c d n m) :
    n = 0 ∧ m = 2 ∧ (e a b c d n m).symm (e a b c d n m f) = f :=
  ⟨hn, hm, (e a b c d n m).symm_apply_apply f⟩

theorem mixed_reconstruct {n m : ℕ} (hn : n = 2) (hm : m = 2)
    (f : Input a b c d n m) :
    n = 2 ∧ m = 2 ∧ (e a b c d n m).symm (e a b c d n m f) = f :=
  ⟨hn, hm, (e a b c d n m).symm_apply_apply f⟩

theorem two_boson_equivalence {n m : ℕ} (hn : n = 0) (hm : m = 2) :
    n = 0 ∧ m = 2 ∧ Nonempty (Input a b c d n m ≃ₗ[ℂ] Output a b c d n m) :=
  ⟨hn, hm, ⟨e a b c d n m⟩⟩

theorem mixed_equivalence {n m : ℕ} (hn : n = 2) (hm : m = 2) :
    n = 2 ∧ m = 2 ∧ Nonempty (Input a b c d n m ≃ₗ[ℂ] Output a b c d n m) :=
  ⟨hn, hm, ⟨e a b c d n m⟩⟩

end Inverses
end
end Math.MixedCompletenessExamples
