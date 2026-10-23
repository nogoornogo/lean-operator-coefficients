import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsOddUpper
import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Complete

/-! The actual C5 coefficient supplies the internal Higgs first-jet rows.
Only explicitly grade-certified primitives are used for invariance. -/
namespace Physics.WeylHiggsInternalLift
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsLorentzUpper
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem even_scalar (s : Label) : evenField s = scalarEmbed (DerivativeLiteratureHiggs.h s.1 s.2) := rfl

theorem rest_scalar (b : Fin 4 → Label) : rest b = scalarEmbed
    (DerivativeLiteratureHiggs.h (b 1).1 (b 1).2 * DerivativeLiteratureHiggs.h (b 2).1 (b 2).2 *
      DerivativeLiteratureHiggs.h (b 3).1 (b 3).2) := by
  simp only [rest,even_scalar,map_mul]

theorem even_word_scalar (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    word c d b 2 (Finsupp.single i 1) (Finsupp.single a 1) (Finsupp.single e 1) =
      psi c a*psi d e*scalarEmbed
        (DerivativeLiteratureHiggs.D i (DerivativeLiteratureHiggs.h (b 0).1 (b 0).2)*
          DerivativeLiteratureHiggs.h (b 1).1 (b 1).2*DerivativeLiteratureHiggs.h (b 2).1 (b 2).2*
            DerivativeLiteratureHiggs.h (b 3).1 (b 3).2) := by
  simp only [word,Math.MixedFirstJetTensor.word,Math.MixedFirstJetTensor.directional_single,
    one_smul,oddField_single,even_scalar,rest_scalar]
  rw [MixedScalarInclusion.derivative]
  simp only [mul_assoc,← map_mul]

def scalarFunctional (f : A →ₗ[ℂ] ℂ) : DerivativeLiteratureHiggs.A →ₗ[ℂ] ℂ :=
  f.comp ((LinearMap.mulLeft ℂ (psi false 0*psi true 0)).comp scalarEmbed.toLinearMap)

theorem scalarFunctional_apply (f : A →ₗ[ℂ] ℂ) (p : DerivativeLiteratureHiggs.A) :
    scalarFunctional f p = f (psi false 0*psi true 0*scalarEmbed p) := rfl

def labels (i j k l : Fin 4) : Fin 4 → Label :=
  ![HiggsQuarticFourInternalControls.label i,HiggsQuarticFourInternalControls.label j,
    HiggsQuarticFourInternalControls.label k,HiggsQuarticFourInternalControls.label l]

theorem mono_word (i j k l : Fin 4) :
    psi false 0*psi true 0*scalarEmbed (HiggsFirstInternal.mono i j k l) =
      word false true (labels i j k l) 2 (Finsupp.single 0 1)
        (Finsupp.single 0 1) (Finsupp.single 0 1) := by
  rw [even_word_scalar]
  rfl

theorem mono_grade (i j k l : Fin 4) :
    psi false 0*psi true 0*scalarEmbed (HiggsFirstInternal.mono i j k l) ∈ V := by
  rw [mono_word]
  exact word_grade false true (labels i j k l) 2 _ _ _

theorem scalar_coordinate (f : A →ₗ[ℂ] ℂ) (i j k l : Fin 4) :
    HiggsFirstInternal.K (scalarFunctional f) i j k l =
      C f false true (labels i j k l) 2 0 0 0 := by
  rw [HiggsFirstInternal.K,scalarFunctional_apply,mono_word,component_word]

theorem paired_internal (g : StandardSMGaugeTensor.GaugeGroup) :
    action (g,1) (psi false 0*psi true 0) = psi false 0*psi true 0 := by
  rw [WeylHiggsCurrent.action_mul,WeylHiggsCurrent.psi_covariant,WeylHiggsCurrent.psi_covariant]
  simp only [map_one,Module.End.one_apply]
  rw [smul_mul_assoc,mul_smul_comm,smul_smul,WeylHiggsCurrent.phases,one_smul]

theorem scalar_internal (g : StandardSMGaugeTensor.GaugeGroup) (p : DerivativeLiteratureHiggs.A) :
    action (g,1) (scalarEmbed p) = scalarEmbed
      (HiggsQuarticFourInternalControls.T g p) := by
  change JetFunctor.mixedAction jets bosons (g,1) (MixedScalarInclusion.embed p) = _
  rw [MixedScalarInclusion.natural]
  change scalarEmbed (HiggsStandardInput.transport (g,1) p) = _
  rw [HiggsStandardInput.factorize]
  have he : HiggsLagrangianInput.transport 1 p = p :=
    congrArg (fun L : Module.End ℂ DerivativeLiteratureHiggs.A => L p) HiggsLagrangianInput.action.map_one
  rw [he]

theorem primitive_internal (g : StandardSMGaugeTensor.GaugeGroup) (p : DerivativeLiteratureHiggs.A) :
    action (g,1) (psi false 0*psi true 0*scalarEmbed p) =
      psi false 0*psi true 0*scalarEmbed (HiggsQuarticFourInternalControls.T g p) := by
  rw [WeylHiggsCurrent.action_mul,paired_internal,scalar_internal]

theorem scalar_invariant (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p)
    (g : StandardSMGaugeTensor.GaugeGroup) (i j k l : Fin 4) :
    scalarFunctional f (HiggsQuarticFourInternalControls.T g (HiggsFirstInternal.mono i j k l)) =
      scalarFunctional f (HiggsFirstInternal.mono i j k l) := by
  rw [scalarFunctional_apply,scalarFunctional_apply,← primitive_internal]
  exact h (g,1) _ (mono_grade i j k l)

end
end Physics.WeylHiggsInternalLift
