import GUT.SU6.SelectionRules.Models.StandardSMUVMass
import Physics.FieldTheory.Mass.OrthogonalMass

open Math

/-! Exact two-block radical, in the actual branching coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6TwoBlockSpectrum
noncomputable section
open Representation InvariantWeylMass StandardSMFullGaugeMass StandardSMUVFields
open SMEpsilonTensor StandardSMGaugeTensor SplitRepresentationProjection

abbrev Five := Color × Weak
abbrev Normal := Light × ((Five × Module.Dual ℂ Five) × (ℂ × Module.Dual ℂ ℂ))

def heavySplit : Heavy ≃ₗ[ℂ] (Five × ℂ) where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualSplit : Module.Dual ℂ Heavy ≃ₗ[ℂ] (Module.Dual ℂ Five × Module.Dual ℂ ℂ) :=
  heavySplit.symm.dualMap.trans (Module.dualProdDualEquivDual ℂ Five ℂ).symm

def normal : Fields ≃ₗ[ℂ] Normal where
  toFun x := (x.1.1, (((heavySplit x.1.2).1, (dualSplit x.2).1),
    ((heavySplit x.1.2).2, (dualSplit x.2).2)))
  invFun x := ((x.1, heavySplit.symm (x.2.1.1, x.2.2.1)),
    dualSplit.symm (x.2.1.2, x.2.2.2))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' a x := by simp

variable (H : Type*) [CommGroup H]
def fiveRho : Representation ℂ (GaugeGroup × H) Five :=
  StandardSMResidualTensor.charged ((twist color (-2)).prod (twist weak 3)) 1

def singletRho : Representation ℂ (GaugeGroup × H) ℂ :=
  StandardSMResidualTensor.charged (Representation.trivial ℂ GaugeGroup ℂ) 1

abbrev normalRho : Representation ℂ (GaugeGroup × H) Normal :=
  (lightRho (neutralCharges H)).prod
    (((fiveRho H).prod (fiveRho H).dual).prod ((singletRho H).prod (singletRho H).dual))

def normalEquiv : Representation.Equiv (StandardSMFullGaugeMass.rho (neutralCharges H))
    (normalRho H) := .mk normal (by
  intro g
  apply LinearMap.ext
  intro x
  ext <;> simp [normal, normalRho, heavySplit, dualSplit, StandardSMFullGaugeMass.rho,
    SplitWeylMass.representation, heavyRho, fiveRho, singletRho,
    StandardSMResidualTensor.charged, Representation.dual])

theorem normalEquiv_apply (x : Fields) : normalEquiv H x = normal x := rfl

def blockMass (a b : ℂ) : SymmetricMass (normalRho H) :=
  OrthogonalMass.prod (SymmetricMass.zero (lightRho (neutralCharges H)))
    (OrthogonalMass.prod (OrthogonalMass.pair (fiveRho H) a)
      (OrthogonalMass.pair (singletRho H) b))

theorem block_finrank (a b : ℂ) :
    Module.finrank ℂ (blockMass H a b).radical.toSubmodule =
      15 + (if a = 0 then 10 else 0) + (if b = 0 then 2 else 0) := by
  rw [blockMass, OrthogonalMass.finrank_prod, OrthogonalMass.finrank_prod,
    (SymmetricMass.zeroRadicalEquiv _).toLinearEquiv.finrank_eq,
    light_finrank, OrthogonalMass.pair_radical, OrthogonalMass.pair_radical]
  have hf : Module.finrank ℂ Five = 5 := by
    simp [Five, Color, Weak, Module.finrank_prod]
  rw [hf]
  simp only [Module.finrank_self, mul_one]
  simp [add_assoc]

attribute [local irreducible] withResidualEquiv

def fieldsMass (a b : ℂ) : SymmetricMass (StandardSMFullGaugeMass.rho (neutralCharges H)) :=
  (EquivariantWeylMassTransport.certificate (normalEquiv H) (blockMass H a b)).mass

def massCertificate (a b : ℂ) :=
  EquivariantWeylMassTransport.certificate (withResidualEquiv H) (fieldsMass H a b)

def mass (a b : ℂ) : SymmetricMass (StandardSMUVMass.rho H) :=
  (massCertificate H a b).mass

theorem block_apply (a b : ℂ) (x y : Normal) : (blockMass H a b).form x y =
    a * (y.2.1.2 x.2.1.1 + x.2.1.2 y.2.1.1) +
    b * (y.2.2.2 x.2.2.1 + x.2.2.2 y.2.2.1) := by
  simp only [blockMass, OrthogonalMass.prod_apply, OrthogonalMass.pair_apply,
    SymmetricMass.zero, LinearMap.zero_apply, zero_add]

theorem normal_block_apply (a b : ℂ) (x y : Fields) :
    (blockMass H a b).form (normal x) (normal y) =
    a * (y.2 (x.1.2.1, (x.1.2.2.1, 0)) + x.2 (y.1.2.1, (y.1.2.2.1, 0))) +
    b * (y.2 (0, (0, x.1.2.2.2)) + x.2 (0, (0, y.1.2.2.2))) := by
  rw [block_apply]
  rfl

theorem fieldsMass_apply (a b : ℂ) (x y : Fields) : (fieldsMass H a b).form x y =
    a * (y.2 (x.1.2.1, (x.1.2.2.1, 0)) + x.2 (y.1.2.1, (y.1.2.2.1, 0))) +
    b * (y.2 (0, (0, x.1.2.2.2)) + x.2 (0, (0, y.1.2.2.2))) := by
  rw [fieldsMass, EquivariantWeylMassTransport.certificate_apply,
    normalEquiv_apply, normalEquiv_apply]
  exact normal_block_apply H a b x y

theorem mass_apply (a b : ℂ) (x y : UV) : (mass H a b).form x y =
    (fieldsMass H a b).form (withResidualEquiv H x) (withResidualEquiv H y) :=
  (massCertificate H a b).apply _ _ x y

def radicalEquiv (a b : ℂ) : Representation.Equiv (mass H a b).radical.toRepresentation
    (blockMass H a b).radical.toRepresentation :=
  (massCertificate H a b).radicalEquiv.trans
    (EquivariantWeylMassTransport.certificate (normalEquiv H) (blockMass H a b)).radicalEquiv

def liftNormal (x : Normal) : UV := (withResidualEquiv H).symm ((normalEquiv H).symm x)

theorem mass_on_normal (a b : ℂ) (x y : Normal) :
    (mass H a b).form (liftNormal H x) (liftNormal H y) =
      (blockMass H a b).form x y := by
  rw [mass, liftNormal, liftNormal,
    EquivariantWeylMassTransport.PullbackCertificate.symm_apply,
    fieldsMass, EquivariantWeylMassTransport.certificate_symm_apply]

def fullRadicalEquiv (a b : ℂ) : Representation.Equiv (mass H a b).radical.toRepresentation
    ((lightRho (neutralCharges H)).prod
      (((OrthogonalMass.pair (fiveRho H) a).radical.toRepresentation).prod
        (OrthogonalMass.pair (singletRho H) b).radical.toRepresentation)) :=
  (radicalEquiv H a b).trans ((OrthogonalMass.radicalEquiv _ _).trans
    (prodEquiv (SymmetricMass.zeroRadicalEquiv _) (OrthogonalMass.radicalEquiv _ _)))

theorem radical_finrank (a b : ℂ) :
    Module.finrank ℂ (mass H a b).radical.toSubmodule =
      15 + (if a = 0 then 10 else 0) + (if b = 0 then 2 else 0) := by
  exact (radicalEquiv H a b).toLinearEquiv.finrank_eq.trans (block_finrank H a b)

def fiveSource : Normal := (0, ((((fun _ => 1), 0), 0), (0, 0)))
def fiveObserver : Normal :=
  (0, ((0, (LinearMap.proj 0).comp (LinearMap.fst ℂ Color Weak)), (0, 0)))
def singletSource : Normal := (0, ((0, 0), (1, 0)))
def singletObserver : Normal := (0, ((0, 0), (0, LinearMap.id)))

theorem five_probe (a b : ℂ) :
    (mass H a b).form (liftNormal H fiveSource) (liftNormal H fiveObserver) = a := by
  rw [mass_on_normal, block_apply]
  simp [fiveSource, fiveObserver]

theorem singlet_probe (a b : ℂ) :
    (mass H a b).form (liftNormal H singletSource) (liftNormal H singletObserver) = b := by
  rw [mass_on_normal, block_apply]
  simp [singletSource, singletObserver]

theorem mass_eq_iff (a b c d : ℂ) : mass H a b = mass H c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · simpa only [five_probe] using congrArg (fun B : SymmetricMass (StandardSMUVMass.rho H) =>
        B.form (liftNormal H fiveSource) (liftNormal H fiveObserver)) h
    · simpa only [singlet_probe] using congrArg (fun B : SymmetricMass (StandardSMUVMass.rho H) =>
        B.form (liftNormal H singletSource) (liftNormal H singletObserver)) h
  · rintro ⟨rfl, rfl⟩
    rfl

end
end GUT.SU6TwoBlockSpectrum
