import GUT.SU6.Yukawa.CouplingEvaluation
import GUT.SU6.Yukawa.LightEquations

open Physics

/-! A full-group invariant nonzero Yukawa that vanishes at the specified vacuum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6InvisibleCoupling
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6FiveCouplings
open SU6IndependentCouplings SU6YukawaLight SU6CouplingEvaluation
attribute [local irreducible] ConcreteWeylBenchmark.matter

def invisible := ProjectedYukawa.diagonal baseYukawa exteriorProjection

theorem invisible_apply (s : StandardSMUVYukawa.scalar.V) (x y : UV) :
    invisible.toLinearMap s x y = baseYukawa.toLinearMap s
      (exteriorProjection x) (exteriorProjection y) := rfl

theorem evaluation_zero (H : Type*) [CommGroup H] :
    invisible.toLinearMap (StandardSMUVYukawa.vacuum H) = 0 := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  rw [invisible_apply, baseYukawa_vacuum, StandardSMUVStabilizer.mass_formula,
    exterior_apply, exterior_apply]
  simp only [map_zero, LinearMap.zero_apply, zero_add]

def squareForm : LinearMap.BilinForm ℂ UV :=
  (LinearMap.mul ℂ ℂ).compl₁₂ (zMap 0) (zMap 0)

theorem squareForm_symm : squareForm.IsSymm := ⟨fun _ _ => mul_comm _ _⟩

def scalarProbe : StandardSMUVYukawa.scalar.V :=
  UnitarySymmetricScalar.algebraEquiv uvRho uv_jointlyContinuous ⟨squareForm, squareForm_symm⟩

theorem scalarProbe_form : baseYukawa.toLinearMap scalarProbe = squareForm := by
  change (((UnitarySymmetricScalar.algebraEquiv uvRho uv_jointlyContinuous).toLinearEquiv.symm
    ((UnitarySymmetricScalar.algebraEquiv uvRho uv_jointlyContinuous).toLinearEquiv
      ⟨squareForm, squareForm_symm⟩))).val = squareForm
  rw [LinearEquiv.symm_apply_apply]

theorem exterior_probe_fixed : exteriorProjection probeQ = probeQ := rfl

theorem z_probe : zMap 0 probeQ = 1 := by
  change contract (exteriorCoordinates exteriorProbe) 0 = 1
  rw [exteriorProbe_contract]
  simp

theorem invisible_probe : invisible.toLinearMap scalarProbe probeQ probeQ = 1 := by
  rw [invisible_apply, scalarProbe_form, exterior_probe_fixed]
  change (zMap 0 probeQ) * (zMap 0 probeQ) = 1
  rw [z_probe, one_mul]

theorem nonzero : ofYukawa invisible ≠ 0 := by
  intro h
  have he := congrArg (fun f : Couplings => (f scalarProbe).val probeQ probeQ) h
  have hp : invisible.toLinearMap scalarProbe probeQ probeQ = 0 := he
  rw [invisible_probe] at hp
  exact one_ne_zero hp

theorem nonzero_kernel (H : Type*) [CommGroup H] :
    ∃ f : Couplings, f ∈ (evaluation H).ker ∧ f ≠ 0 := by
  refine ⟨ofYukawa invisible, ?_, nonzero⟩
  change evaluation H (ofYukawa invisible) = 0
  rw [evaluation_ofYukawa, evaluation_zero]

end
end GUT.SU6InvisibleCoupling
