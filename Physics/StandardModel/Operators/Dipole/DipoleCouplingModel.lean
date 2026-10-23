import Physics.StandardModel.Operators.Dipole.DipoleMediatorPaths
import Math.LinearAlgebra.Selection.BilinearSelectedPaths

open Math

/-! A compositional coupling model whose finite paths are derived from bases.
The kernel law is algebraic input, not a calculated UV matching law. -/
namespace Physics.DipoleCouplingModel
set_option autoImplicit false
noncomputable section
open Representation

variable {H A B M X Y : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (m : Representation ℂ H M)

structure Couplings where
  incoming : X →ₗ[ℂ] IntertwiningMap a m
  outgoingB : Y →ₗ[ℂ] IntertwiningMap m b
  outgoingW : Y →ₗ[ℂ] IntertwiningMap m b
  propagator : IntertwiningMap m m

variable (model : Couplings (X := X) (Y := Y) a b m)

def residual (x : X) (y : Y) : IntertwiningMap a b × IntertwiningMap a b :=
  ((model.outgoingB y).comp (model.propagator.comp (model.incoming x)),
    (model.outgoingW y).comp (model.propagator.comp (model.incoming x)))

def channel (v : Y →ₗ[ℂ] IntertwiningMap m b) : X →ₗ[ℂ] Y →ₗ[ℂ] IntertwiningMap a b where
  toFun x := ((IntertwiningMap.llcomp a m b).flip
    ((IntertwiningMap.llcomp a m m model.propagator) (model.incoming x))).comp v
  map_add' x z := by apply LinearMap.ext; intro y; simp
  map_smul' c x := by apply LinearMap.ext; intro y; simp

def bilinear : X →ₗ[ℂ] Y →ₗ[ℂ] (IntertwiningMap a b × IntertwiningMap a b) where
  toFun x := (channel a b m model model.outgoingB x).prod
    (channel a b m model model.outgoingW x)
  map_add' x z := by apply LinearMap.ext; intro y; simp
  map_smul' c x := by apply LinearMap.ext; intro y; simp

@[simp] theorem bilinear_apply (x : X) (y : Y) :
    bilinear a b m model x y = residual a b m model x y := rfl

variable [FiniteDimensional ℂ B]

def generation (x : X) (y : Y) : DipoleFlavorSelection.Coefficients a b :=
  (DipoleSMCoefficient.equiv a b).symm (residual a b m model x y)

@[simp] theorem generation_residual (x : X) (y : Y) :
    (DipoleSMCoefficient.equiv a b) (generation a b m model x y) =
      residual a b m model x y := LinearEquiv.apply_symm_apply _ _

theorem selected (mu : A) (electron : Module.Dual ℂ B) (x : X) (y : Y) :
    DipoleFlavorSelection.selector a b mu electron (generation a b m model x y) =
    (electron (model.outgoingB y (model.propagator (model.incoming x mu))),
      electron (model.outgoingW y (model.propagator (model.incoming x mu)))) := by
  change DipoleFlavorSelection.residualSelector a b mu electron
    ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem generation_zero_of_propagator_zero (hT : model.propagator = 0) (x : X) (y : Y) :
    generation a b m model x y = 0 := by
  apply (DipoleSMCoefficient.equiv a b).injective
  simp [generation_residual, residual, hT, IntertwiningMap.comp_def]

variable {J K : Type*} [Fintype J] [Fintype K]
  (bx : Module.Basis J ℂ X) (by_ : Module.Basis K ℂ Y)

omit [FiniteDimensional ℂ B] in
theorem residual_expansion (x : X) (y : Y) : residual a b m model x y =
    WeightedSelectedPaths.synthesis
      (BilinearSelectedPaths.paths (bilinear a b m model) bx by_)
      (BilinearSelectedPaths.weights bx by_) (x,y) :=
  BilinearSelectedPaths.expansion (bilinear a b m model) bx by_ x y

/-- The previously assumed residual factorization is derived for this model. -/
theorem generation_factorization (x : X) (y : Y) :
    (DipoleSMCoefficient.equiv a b) (generation a b m model x y) =
    WeightedSelectedPaths.synthesis
      (BilinearSelectedPaths.paths (bilinear a b m model) bx by_)
      (BilinearSelectedPaths.weights bx by_) (x,y) := by
  rw [generation_residual, residual_expansion a b m model bx by_]

omit [FiniteDimensional ℂ B] [Fintype J] [Fintype K] in
/-- Identify the derived basis paths with the existing mediator-path interface. -/
theorem basis_paths : BilinearSelectedPaths.paths (bilinear a b m model) bx by_ =
    DipoleMediatorPaths.paths a b m
      (fun i : J × K => model.propagator.comp (model.incoming (bx i.1)))
      (fun i => model.outgoingB (by_ i.2))
      (fun i => model.outgoingW (by_ i.2)) := rfl

theorem generation_eq_paths (x : X) (y : Y) : generation a b m model x y =
    DipoleMediatorPaths.generation a b m
      (fun i : J × K => model.propagator.comp (model.incoming (bx i.1)))
      (fun i => model.outgoingB (by_ i.2))
      (fun i => model.outgoingW (by_ i.2))
      (BilinearSelectedPaths.weights bx by_) (x,y) := by
  apply (DipoleSMCoefficient.equiv a b).injective
  rw [generation_factorization a b m model bx by_, basis_paths]
  simp only [DipoleMediatorPaths.generation, LinearEquiv.apply_symm_apply]

theorem exists_nonzero_iff_basis_path (mu : A) (electron : Module.Dual ℂ B) :
    (∃ x y, DipoleFlavorSelection.selector a b mu electron
      (generation a b m model x y) ≠ 0) ↔
    ∃ i : J × K,
      electron (model.outgoingB (by_ i.2)
        (model.propagator (model.incoming (bx i.1) mu))) ≠ 0 ∨
      electron (model.outgoingW (by_ i.2)
        (model.propagator (model.incoming (bx i.1) mu))) ≠ 0 := by
  have h := BilinearSelectedPaths.exists_nonzero_iff_basis_path
    (bilinear a b m model) bx by_ (DipoleFlavorSelection.residualSelector a b mu electron)
  have he : ∀ x y, DipoleFlavorSelection.selector a b mu electron
      (generation a b m model x y) =
      DipoleFlavorSelection.residualSelector a b mu electron (bilinear a b m model x y) := by
    intro x y
    change DipoleFlavorSelection.residualSelector a b mu electron
      ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simpa only [he, bilinear_apply, residual, DipoleFlavorSelection.residualSelector,
    DipoleFlavorSelection.evaluation, LinearMap.coe_mk, AddHom.coe_mk,
    IntertwiningMap.comp_apply, ne_eq, Prod.ext_iff,
    Prod.fst_zero, Prod.snd_zero, not_and_or] using h

omit [Fintype J] [Fintype K] in
theorem nonzero_at_basis_witness (mu : A) (electron : Module.Dual ℂ B) (i : J × K)
    (hi : electron (model.outgoingB (by_ i.2)
      (model.propagator (model.incoming (bx i.1) mu))) ≠ 0 ∨
      electron (model.outgoingW (by_ i.2)
      (model.propagator (model.incoming (bx i.1) mu))) ≠ 0) :
    DipoleFlavorSelection.selector a b mu electron
      (generation a b m model (bx i.1) (by_ i.2)) ≠ 0 := by
  rw [selected]
  simpa only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or] using hi

theorem parameterized_factorization {Z : Type*} (u : Z → X) (v : Z → Y) (z : Z) :
    (DipoleSMCoefficient.equiv a b) (generation a b m model (u z) (v z)) =
    WeightedSelectedPaths.synthesis
      (BilinearSelectedPaths.paths (bilinear a b m model) bx by_)
      (fun t => BilinearSelectedPaths.weights bx by_ (u t, v t)) z :=
  generation_factorization a b m model bx by_ (u z) (v z)

end
end Physics.DipoleCouplingModel
