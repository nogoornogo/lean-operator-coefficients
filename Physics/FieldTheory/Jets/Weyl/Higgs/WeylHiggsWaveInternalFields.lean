import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveMoments
import Math.Algebra.Jets.ColoredFirstJetFields

/-! The wave sum's internal first-jet moments are a marked invariant
quartic pairing. The model is proved on all field-vector arguments. -/
namespace Physics.WeylHiggsWaveInternalFields
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput
open WeylHiggsEvenValue WeylHiggsWaveWords WeylHiggsWaveMoments
abbrev Fields := ColoredWavePairing.Fields
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def onScalar (c d : Bool) (a e : Fin 2) : DerivativeLiteratureHiggs.A →ₗ[ℂ] ℂ :=
  WeylHiggsWaveSum.functional.comp
    ((LinearMap.mulLeft ℂ (psi c a*psi d e)).comp scalarEmbed.toLinearMap)
theorem onScalar_apply (c d : Bool) (a e : Fin 2) (p : DerivativeLiteratureHiggs.A) :
    onScalar c d a e p = WeylHiggsWaveSum.functional (psi c a*psi d e*scalarEmbed p) := rfl

def amplitude (c d : Bool) (a e : Fin 2) (i : Fin 4) : ℂ :=
  if c then if d then 0 else -(2*WeylDirectionInvariant.kernel e a i)
  else if d then 2*WeylDirectionInvariant.kernel a e i else 0

def fieldTensor (c d : Bool) (a e : Fin 2) (i : Fin 4) :
    MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ :=
  (onScalar c d a e).compMultilinearMap (ColoredFirstJetFields.first (ColoredQuarticWords.E i))

theorem fieldTensor_model (c d : Bool) (a e : Fin 2) (i : Fin 4) :
    fieldTensor c d a e i = amplitude c d a e i • MarkedFieldPairing.marked := by
  apply ColoredFirstJetFields.multilinear_ext
  intro b
  simp only [fieldTensor,LinearMap.compMultilinearMap_apply,ColoredFirstJetFields.first_basis,
    _root_.smul_apply,smul_eq_mul]
  change WeylHiggsWaveSum.functional (psi c a*psi d e*scalarEmbed (scalarMono b i)) =
    amplitude c d a e i*marked b
  cases c <;> cases d
  · simp only [functional_scalar_same,amplitude,Bool.false_eq_true,ite_false,zero_mul]
  · exact left_even b a e i
  · exact right_even b a e i
  · simp only [functional_scalar_same,amplitude,ite_true,zero_mul]

theorem first_covariant {H : Type*} [Group H] (rho : Representation ℂ H (Fin 2 → ℂ))
    (g : H) (i : Fin 4) (v : Fin 4 → Fields) :
    HiggsInternalSymmetry.transport rho g (ColoredFirstJetFields.first (ColoredQuarticWords.E i) v) =
      ColoredFirstJetFields.first (ColoredQuarticWords.E i)
        (fun t => PairedComponentFields.action rho g (v t)) := by
  rw [ColoredFirstJetFields.first_apply,ColoredFirstJetFields.first_apply]
  simp only [ColoredQuarticWords.dirD_single,one_smul]
  change HiggsInternalSymmetry.transport rho g
    (DerivativeLiteratureHiggs.D i (HiggsInternalSymmetry.fields (v 0))*
      HiggsInternalSymmetry.fields (v 1)*HiggsInternalSymmetry.fields (v 2)*HiggsInternalSymmetry.fields (v 3)) = _
  simp only [map_mul,HiggsInternalSymmetry.derivative_commute,HiggsInternalSymmetry.fields_covariant]
  rfl

theorem scalar_invariant (g : StandardSMGaugeTensor.GaugeGroup) (c d : Bool) (a e : Fin 2)
    (b : Fin 4 → Label) (i : Fin 4) :
    onScalar c d a e (HiggsQuarticFourInternalControls.T g (scalarMono b i)) =
      onScalar c d a e (scalarMono b i) := by
  have hb : ColoredFirstJetFields.first (ColoredQuarticWords.E i)
      (fun t => Finsupp.single (b t) 1) = scalarMono b i := by
    rw [ColoredFirstJetFields.first_basis]
    rfl
  rw [← hb,first_covariant]
  change fieldTensor c d a e i
    (fun t => PairedComponentFields.action HiggsFieldDictionary.higgs g (Finsupp.single (b t) 1)) =
      fieldTensor c d a e i (fun t => Finsupp.single (b t) 1)
  rw [fieldTensor_model]
  simp only [_root_.smul_apply,MarkedFieldPairing.marked_invariant]

end
end Physics.WeylHiggsWaveInternalFields
