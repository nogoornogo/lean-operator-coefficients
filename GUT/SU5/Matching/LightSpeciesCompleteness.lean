import GUT.SU5.Matching.LightSpeciesExchange
import Physics.StandardModel.Operators.MediatorFullLightCertificate
import Lean.LibrarySuggestions.Basic

/-! The generated exchange, rather than an independently chosen allowed
coefficient, in the complete actual light-species sector and residual Hom. -/
set_option autoImplicit false
-- The concrete sector's type is too large for premise-selection indexing.
-- This affects search suggestions only, not kernel checking or axiom audits.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "LightSpeciesCompleteness"
namespace GUT.SU5.LightSpeciesCompleteness
noncomputable section
open Representation MatterSource LightSpeciesMaps LightSpeciesExchange
open SMEpsilonTensor StandardSMGaugeTensor
open scoped TensorProduct
variable {H : Type*} [Group H] {n : ℕ} (R : OrdinaryAction H n)

local instance : AddCommGroup Quark := inferInstance

def generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorQque.sector (qRep R) (uRep R) (eRep R) (MediatorMatching.mass g v hg hv)
    (g : ℂ) (leftCurrent R) (rightCurrent R) (invariant R g v hg hv)

private theorem probe_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorMatching.coefficient g v hg hv
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1)) ⊗ₜ[ℂ]
        (colorBasis 2 ⊗ₜ[ℂ] (1 : ℂ))) *
      (eps2 (weakBasis 0) (weakBasis 1) * eps2 (weakBasis 0) (weakBasis 1)) -
    MediatorMatching.coefficient g v hg hv
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0)) ⊗ₜ[ℂ]
        (colorBasis 2 ⊗ₜ[ℂ] (1 : ℂ))) *
      (eps2 (weakBasis 1) (weakBasis 0) * eps2 (weakBasis 0) (weakBasis 1)) ≠ 0 := by
  simp only [MediatorMatching.coefficient_eq, LinearMap.smul_apply, smul_eq_mul, qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]
  exact TreeMatching.orderedWilson_ne_zero hg hv

def certificate (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    MediatorFullLightCertificate.Certificate (tau R)
      (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R) :=
  MediatorFullLightCertificate.ofRestriction (tau R)
    (MediatorMatching.mass g v hg hv) (g : ℂ) (leftCurrent R) (rightCurrent R)
    (invariant R g v hg hv)
    (Q R a) (U R a) (E R a) (MediatorMatching.coefficient g v hg hv)
    (fun x y u e => (coefficient_generations R g v hg hv a a a a x y u e).trans
      (ite_eq_left ⟨rfl, rfl⟩))
    (colorBasis 0 ⊗ₜ[ℂ] weakBasis 0)
    (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) (colorBasis 2) 1
    (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
    (probe_nonzero g v hg hv)

theorem certificate_generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    (certificate R g v hg hv a).generated = generated R g v hg hv := rfl

theorem generated_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    generated R g v hg hv ≠ 0 :=
  (certificate R g v hg hv a).generated_nonzero

def residualHom (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : FullLightSpeciesQque.ResidualHom (tau R) :=
  (FullLightSpeciesQque.equiv (tau R) (sm_semisimple R)).symm (generated R g v hg hv)

theorem certificate_residualHom (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    (certificate R g v hg hv a).residualHom (sm_semisimple R) =
      residualHom R g v hg hv := rfl

theorem reconstruct (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    FullLightSpeciesQque.equiv (tau R) (sm_semisimple R) (residualHom R g v hg hv) =
      generated R g v hg hv :=
  (FullLightSpeciesQque.equiv (tau R) (sm_semisimple R)).apply_symm_apply (generated R g v hg hv)

theorem residualHom_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (a : Fin n) :
    residualHom R g v hg hv ≠ 0 :=
  (certificate R g v hg hv a).residualHom_nonzero (sm_semisimple R)

theorem hasCoefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (hn : 0 < n) :
    FullLightSpeciesQque.HasCoefficient (tau R) :=
  ⟨generated R g v hg hv, generated_nonzero R g v hg hv ⟨0, hn⟩⟩

theorem hasResidualMap (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (hn : 0 < n) :
    FullLightSpeciesQque.HasResidualMap (tau R) :=
  ⟨residualHom R g v hg hv, residualHom_nonzero R g v hg hv ⟨0, hn⟩⟩

theorem one_generation (R1 : OrdinaryAction H 1) (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    generated R1 g v hg hv ≠ 0 := generated_nonzero R1 g v hg hv 0

theorem three_generations (R3 : OrdinaryAction H 3) (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    generated R3 g v hg hv ≠ 0 := generated_nonzero R3 g v hg hv 0

end
end GUT.SU5.LightSpeciesCompleteness
