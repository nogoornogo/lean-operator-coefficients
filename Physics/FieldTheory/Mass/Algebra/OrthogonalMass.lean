import Physics.FieldTheory.Mass.Spectrum.ScaledMassSpectrum
import Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary

/-! Orthogonal sums preserve the entire radical as a product representation. -/
set_option autoImplicit false
namespace Physics.OrthogonalMass
noncomputable section
open Representation InvariantWeylMass
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G V} {sigma : Representation ℂ G W}

def prod (B : SymmetricMass rho) (D : SymmetricMass sigma) : SymmetricMass (rho.prod sigma) where
  form := B.form.compl₁₂ (LinearMap.fst ℂ V W) (LinearMap.fst ℂ V W) +
    D.form.compl₁₂ (LinearMap.snd ℂ V W) (LinearMap.snd ℂ V W)
  symmetric := ⟨fun x y => congrArg₂ (· + ·) (B.symmetric.eq x.1 y.1) (D.symmetric.eq x.2 y.2)⟩
  invariant g x y := congrArg₂ (· + ·) (B.invariant g x.1 y.1) (D.invariant g x.2 y.2)

theorem prod_apply (B : SymmetricMass rho) (D : SymmetricMass sigma) (x y : V × W) :
    (prod B D).form x y = B.form x.1 y.1 + D.form x.2 y.2 := rfl

theorem mem_radical (B : SymmetricMass rho) (D : SymmetricMass sigma) (x : V × W) :
    x ∈ (prod B D).radical.toSubmodule ↔
      x.1 ∈ B.radical.toSubmodule ∧ x.2 ∈ D.radical.toSubmodule := by
  simp only [SymmetricMass.mem_radical]
  constructor
  · intro h
    constructor
    · intro v
      simpa [prod] using h (v, 0)
    · intro w
      simpa [prod] using h (0, w)
  · rintro ⟨hB, hD⟩ y
    change B.form x.1 y.1 + D.form x.2 y.2 = 0
    rw [hB, hD, zero_add]

def radicalEquiv (B : SymmetricMass rho) (D : SymmetricMass sigma) :
    Representation.Equiv (prod B D).radical.toRepresentation
      (B.radical.toRepresentation.prod D.radical.toRepresentation) where
  toLinearEquiv :=
    { toFun := fun x => (⟨x.val.1, ((mem_radical B D x.val).mp x.property).1⟩,
        ⟨x.val.2, ((mem_radical B D x.val).mp x.property).2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val), (mem_radical B D _).mpr ⟨x.1.property, x.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem finrank_prod [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (B : SymmetricMass rho) (D : SymmetricMass sigma) :
    Module.finrank ℂ (prod B D).radical.toSubmodule =
      Module.finrank ℂ B.radical.toSubmodule + Module.finrank ℂ D.radical.toSubmodule := by
  rw [(radicalEquiv B D).toLinearEquiv.finrank_eq, Module.finrank_prod]

def pair (rho : Representation ℂ G V) (c : ℂ) :=
  ScaledMassSpectrum.mass (LightInheritanceBoundary.pairedMass rho) c

theorem pair_apply (rho : Representation ℂ G V) (c : ℂ)
    (x y : V × Module.Dual ℂ V) :
    (pair rho c).form x y = c * (y.2 x.1 + x.2 y.1) := rfl

theorem pair_radical [FiniteDimensional ℂ V] (rho : Representation ℂ G V) (c : ℂ) :
    Module.finrank ℂ (pair rho c).radical.toSubmodule =
      if c = 0 then 2 * Module.finrank ℂ V else 0 := by
  by_cases h : c = 0
  · subst c
    rw [pair, ScaledMassSpectrum.zero_mass, ite_eq_left rfl]
    rw [(SymmetricMass.zeroRadicalEquiv _).toLinearEquiv.finrank_eq, Module.finrank_prod,
      Subspace.dual_finrank_eq]
    omega
  · rw [ite_eq_right h, pair, ScaledMassSpectrum.radical_finrank _ _ h,
      LightInheritanceBoundary.paired_radical_eq_bot]
    simp

end
end Physics.OrthogonalMass
