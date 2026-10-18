import Math.RepresentationTheory.IsotypicResidual
import Math.RepresentationTheory.DirectSumResidualHom
import Mathlib.RepresentationTheory.Maschke

/-! A commuting residual action is linear over the statistics group algebra.
Thus the intrinsic isotypic splitting applies even to infinite flavor modules. -/
namespace Math.CommutingStatisticsModule
set_option autoImplicit false
noncomputable section
open Representation
open scoped MonoidAlgebra
variable {k H S U : Type*} [Field k] [Group H] [Group S]
  [AddCommGroup U] [Module k U]
  (rho : Representation k H U) (b : Representation k S U)
  (commutes : ∀ g h u, b g (rho h u) = rho h (b g u))

def action : Representation k[S] H b.asModule where
  toFun h :=
    { toFun := fun u => b.asModuleEquiv.symm (rho h (b.asModuleEquiv u))
      map_add' := by intros; simp
      map_smul' r u := by
        change b.asModuleEquiv.symm (rho h (b.asModuleEquiv (r • u))) =
          r • b.asModuleEquiv.symm (rho h (b.asModuleEquiv u))
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add r s hr hs => rw [add_smul, map_add, map_add, map_add, hr, hs, add_smul]
        | single g z =>
          apply b.asModuleEquiv.injective
          simp only [LinearEquiv.apply_symm_apply, b.asModuleEquiv_map_smul,
            Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
          exact congrArg (fun v => z • v) (commutes g h (b.asModuleEquiv u)).symm }
  map_one' := by ext u; simp
  map_mul' h j := by ext u; simp [map_mul, Module.End.mul_apply]

@[simp] theorem action_apply (h : H) (u : b.asModule) :
    b.asModuleEquiv (action rho b commutes h u) = rho h (b.asModuleEquiv u) :=
  b.asModuleEquiv.apply_symm_apply _

section Finite
variable [Finite S] [NeZero (Nat.card S : k)]

/-- Actual independent isotypic components, each with arbitrary multiplicity. -/
def decomposition := IsotypicResidual.sumEquiv (action rho b commutes)

abbrev Index := IsotypicResidual.Index (R := k[S]) (M := b.asModule)

def residual : Representation k H b.asModule where
  toFun h := (action rho b commutes h).restrictScalars k
  map_one' := by ext u; exact congrArg (fun f => f u) (action rho b commutes).map_one
  map_mul' h j := by
    ext u
    exact congrArg (fun f => f u) ((action rho b commutes).map_mul h j)

def block (c : Index b) : Representation k H c.1 where
  toFun h := (IsotypicResidual.component (action rho b commutes) c h).restrictScalars k
  map_one' := by
    apply LinearMap.ext
    intro u
    exact congrArg (fun f => f u)
      (IsotypicResidual.component (action rho b commutes) c).map_one
  map_mul' h j := by
    apply LinearMap.ext
    intro u
    exact congrArg (fun f => f u)
      ((IsotypicResidual.component (action rho b commutes) c).map_mul h j)

/-- Scalar-level splitting, retaining only residual equivariance. -/
def scalarDecomposition : Representation.Equiv
    (Representation.directSum (block rho b commutes)) (residual rho b commutes) where
  toLinearEquiv := (decomposition rho b commutes).toLinearEquiv.restrictScalars k
  isIntertwining' h := by
    apply LinearMap.ext
    intro u
    exact IntertwiningMap.isIntertwining _ _ (decomposition rho b commutes).toIntertwiningMap h u

def carrierEquiv : Representation.Equiv (residual rho b commutes) rho where
  toLinearEquiv := b.asModuleEquiv
  isIntertwining' h := by ext u; exact action_apply rho b commutes h u

/-- Nonredundant splitting of the original carrier by statistics types. -/
def equiv : Representation.Equiv (Representation.directSum (block rho b commutes)) rho :=
  (scalarDecomposition rho b commutes).trans (carrierEquiv rho b commutes)

@[simp] theorem equiv_single (c : Index b) (u : c.1) :
    equiv rho b commutes (DFinsupp.single c u) = b.asModuleEquiv u := by
  exact congrArg b.asModuleEquiv
    (IsotypicResidual.sumEquiv_single (action rho b commutes) c u)

variable {W : Type*} [AddCommGroup W] [Module k W] (w : Representation k H W)

/-- Residual Hom is a product over distinct statistics isotypic components. -/
def coefficientEquiv : IntertwiningMap rho w ≃ₗ[k]
    (∀ c : Index b, IntertwiningMap (block rho b commutes c) w) := by
  classical
  exact DirectSumResidualHom.coefficientEquiv (block rho b commutes) w
    (equiv rho b commutes)

@[simp] theorem coefficientEquiv_apply (f : IntertwiningMap rho w)
    (c : Index b) (u : c.1) :
    coefficientEquiv rho b commutes w f c u = f (b.asModuleEquiv u) := by
  classical
  change f (equiv rho b commutes (DFinsupp.single c u)) = _
  rw [equiv_single]

theorem coefficient_zero_iff (f : IntertwiningMap rho w) :
    f = 0 ↔ ∀ c, coefficientEquiv rho b commutes w f c = 0 := by
  rw [← (coefficientEquiv rho b commutes w).map_eq_zero_iff]
  exact funext_iff

end Finite
end
end Math.CommutingStatisticsModule
