import GUT.SU5.Matching.LightRadical
import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQqueEvaluation

open Physics

open Math

/-! Exchange on actual massless matter and its dual, invariant under the
ordinary centralizer. Its retained-field restriction is the original qque
exchange. The ambient endpoint here is H x Lorentz, not yet SM x H. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.LightRadicalExchange
noncomputable section
open MatterSource LightRadical HeavyCurrents ExteriorSquareCoordinates
open SMEpsilonTensor StandardSMGaugeTensor
open scoped TensorProduct

variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

local instance : AddCommGroup (Light R) := inferInstance
local instance : Module ℂ (Light R) := inferInstance
local instance : AddCommGroup (Module.Dual ℂ (Light R)) := inferInstance
local instance : AddCommGroup (Light R ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (Module.Dual ℂ (Light R) ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance

def leftCurrent : Light R ⊗[ℂ] Module.Dual ℂ (Light R) →ₗ[ℂ] MediatorMatching.Channels :=
  LinearMap.pi fun i => LinearMap.pi fun w =>
    TensorProduct.lift (current R (infinitesimal (upper i w)))

def rightCurrent : Light R ⊗[ℂ] Module.Dual ℂ (Light R) →ₗ[ℂ]
    Module.Dual ℂ MediatorMatching.Channels :=
  MediatorMatching.pairing.comp (LinearMap.pi fun i => LinearMap.pi fun w =>
    TensorProduct.lift (current R (infinitesimal (lower i w))))

theorem left_invariant (h : H) (x : Light R) (phi : Module.Dual ℂ (Light R)) :
    leftCurrent R (lightResidual R h x ⊗ₜ[ℂ] (lightResidual R).dual h phi) =
      leftCurrent R (x ⊗ₜ[ℂ] phi) := by
  funext i w
  exact current_invariant R _ h x phi

theorem right_invariant (h : H) (x : Light R) (phi : Module.Dual ℂ (Light R)) :
    rightCurrent R (lightResidual R h x ⊗ₜ[ℂ] (lightResidual R).dual h phi) =
      rightCurrent R (x ⊗ₜ[ℂ] phi) := by
  apply congrArg MediatorMatching.pairing
  funext i w
  exact current_invariant R _ h x phi

def coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorExchange.coefficient (MediatorMatching.mass g v hg hv) (g : ℂ)
    (leftCurrent R) (rightCurrent R)

theorem invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorQque.IsInvariant (lightResidual R) (lightResidual R).dual (lightResidual R).dual
      (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R) := by
  intro h z
  have he : (coefficient R g v hg hv).comp
      (((lightResidual R).tprod (lightResidual R)).tprod
        ((lightResidual R).dual.tprod (lightResidual R).dual) h) = coefficient R g v hg hv := by
    apply TensorProduct.ext_fourfold'
    intro x y phi psi
    change coefficient R g v hg hv
      ((lightResidual R h x ⊗ₜ[ℂ] lightResidual R h y) ⊗ₜ[ℂ]
        ((lightResidual R).dual h phi ⊗ₜ[ℂ] (lightResidual R).dual h psi)) = _
    simp only [coefficient, MediatorExchange.coefficient_tmul, left_invariant, right_invariant]
  exact DFunLike.congr_fun he z

theorem left_on_fields (a : Fin n) (q : StandardSMGaugeTensor.Quark) (u : Color) :
    leftCurrent R (LightRadical.quark R a q ⊗ₜ[ℂ] up R a u) =
      MediatorMatching.leftCurrent (q ⊗ₜ[ℂ] u) := by
  funext i w
  exact up_current R a i w q u

theorem right_on_fields (a : Fin n) (q : StandardSMGaugeTensor.Quark) (e : ℂ) :
    rightCurrent R (LightRadical.quark R a q ⊗ₜ[ℂ] electron R a e) =
      MediatorMatching.rightCurrent (q ⊗ₜ[ℂ] e) := by
  apply congrArg MediatorMatching.pairing
  funext i w
  exact electron_current R a i w q e

theorem coefficient_on_fields (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (a : Fin n) (q s : StandardSMGaugeTensor.Quark) (u : Color) (e : ℂ) :
    coefficient R g v hg hv
      ((LightRadical.quark R a q ⊗ₜ[ℂ] LightRadical.quark R a s) ⊗ₜ[ℂ]
        (up R a u ⊗ₜ[ℂ] electron R a e)) =
      MediatorMatching.coefficient g v hg hv ((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) := by
  simp only [coefficient, MediatorMatching.coefficient, MediatorExchange.coefficient_tmul,
    left_on_fields, right_on_fields]

def generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorQque.sector (lightResidual R) (lightResidual R).dual (lightResidual R).dual
    (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R)
    (invariant R g v hg hv)

theorem exterior_on_fields (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (a : Fin n) (q s : StandardSMGaugeTensor.Quark) (u : Color) (e : ℂ)
    (z t l k : WeylSpinor.Space) :
    (generated R g v hg hv).val (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (LightRadical.quark R a q ⊗ₜ[ℂ] z) (LightRadical.quark R a s ⊗ₜ[ℂ] t)
      (up R a u ⊗ₜ[ℂ] l) (electron R a e ⊗ₜ[ℂ] k))) =
    TreeMatching.matchedExterior g v (exteriorPower.ιMulti ℂ 4
      (FourSlotAlternation.slots (q ⊗ₜ[ℂ] z) (s ⊗ₜ[ℂ] t) (u ⊗ₜ[ℂ] l) (e ⊗ₜ[ℂ] k))) := by
  refine (MediatorQqueEvaluation.sector_slots (lightResidual R) (lightResidual R).dual
    (lightResidual R).dual (MediatorMatching.mass g v hg hv) (g : ℂ)
    (leftCurrent R) (rightCurrent R) (invariant R g v hg hv)
    (LightRadical.quark R a q) (LightRadical.quark R a s)
    (up R a u) (electron R a e) z t l k).trans ?_
  change coefficient R g v hg hv _ * _ - coefficient R g v hg hv _ * _ = _
  rw [coefficient_on_fields, coefficient_on_fields, MediatorMatching.coefficient_eq]
  rw [TreeMatching.matchedExterior, QqueSpinorExterior.exterior,
    FourSlotAlternation.coefficient_slots]
  rfl

theorem generated_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    generated R g v hg hv ≠ 0 := by
  apply MediatorQqueEvaluation.sector_ne_zero_of_slots
    (lightResidual R) (lightResidual R).dual (lightResidual R).dual
    (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R)
    (invariant R g v hg hv)
    (LightRadical.quark R a (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0))
    (LightRadical.quark R a (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1))
    (up R a (colorBasis 2)) (electron R a 1)
    (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
  change coefficient R g v hg hv _ * _ - coefficient R g v hg hv _ * _ ≠ 0
  rw [coefficient_on_fields, coefficient_on_fields, MediatorMatching.coefficient_eq]
  simp only [LinearMap.smul_apply, smul_eq_mul, qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]
  exact TreeMatching.orderedWilson_ne_zero hg hv

theorem one_generation (R1 : OrdinaryAction H 1) (g v : ℝ)
    (hg : g ≠ 0) (hv : v ≠ 0) : generated R1 g v hg hv ≠ 0 :=
  generated_nonzero R1 g v hg hv 0

theorem three_generations (R3 : OrdinaryAction H 3) (g v : ℝ)
    (hg : g ≠ 0) (hv : v ≠ 0) : generated R3 g v hg hv ≠ 0 :=
  generated_nonzero R3 g v hg hv 0

end
end GUT.SU5.LightRadicalExchange
