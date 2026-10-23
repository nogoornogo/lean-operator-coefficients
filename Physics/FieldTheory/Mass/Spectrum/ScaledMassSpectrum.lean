import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass

/-! Exact zero-mode representation of a scalar multiple of a symmetric mass. -/
set_option autoImplicit false
namespace Physics.ScaledMassSpectrum
noncomputable section
open InvariantWeylMass Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {rho : Representation ℂ G V} (B : SymmetricMass rho) (c : ℂ)

def mass : SymmetricMass rho where
  form := c • B.form
  symmetric := B.symmetric.smul c
  invariant g x y := by
    change c * B.form (rho g x) (rho g y) = c * B.form x y
    rw [B.invariant]

theorem mass_apply (x y : V) : (mass B c).form x y = c * B.form x y := rfl

theorem zero_mass : mass B 0 = SymmetricMass.zero rho := by
  apply SymmetricMass.ext
  simp [mass, SymmetricMass.zero]

theorem one_mass : mass B 1 = B := by
  apply SymmetricMass.ext
  simp [mass]

theorem form_nonzero (hc : c ≠ 0) (hB : B.form ≠ 0) : (mass B c).form ≠ 0 :=
  smul_ne_zero hc hB

theorem mem_radical_iff (hc : c ≠ 0) (x : V) :
    x ∈ (mass B c).radical.toSubmodule ↔ x ∈ B.radical.toSubmodule := by
  simp only [SymmetricMass.mem_radical, mass_apply, mul_eq_zero, hc, false_or]

def radicalEquiv (hc : c ≠ 0) :
    Representation.Equiv (mass B c).radical.toRepresentation B.radical.toRepresentation where
  toLinearEquiv :=
    { toFun := fun x => ⟨x.val, (mem_radical_iff B c hc x.val).mp x.property⟩
      invFun := fun x => ⟨x.val, (mem_radical_iff B c hc x.val).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem radical_finrank [FiniteDimensional ℂ V] (hc : c ≠ 0) :
    Module.finrank ℂ (mass B c).radical.toSubmodule = Module.finrank ℂ B.radical.toSubmodule :=
  (radicalEquiv B c hc).toLinearEquiv.finrank_eq

theorem radical_character [FiniteDimensional ℂ V] (hc : c ≠ 0) (g : G) :
    (mass B c).radical.toRepresentation.character g = B.radical.toRepresentation.character g :=
  congrFun (Representation.char_iso (radicalEquiv B c hc)) g

end
end Physics.ScaledMassSpectrum
