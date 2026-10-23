import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaves

/-! Exact values of the full-relation wave probes on the C5 current. -/
namespace Physics.WeylHiggsWaveValues
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsWaves
open scoped TensorProduct
abbrev ev (p : Fin 4 → ℂ) (x y : Fin 2) :=
  ColoredFourWaveEvaluation.evaluation (momenta p) (ColoredWavePairing.amplitudes x y)

theorem first (p : Fin 4 → ℂ) (x y : Fin 2) (i : Fin 4) (c : Bool) (a : Fin 2) :
    ev p x y (DerivativeLiteratureHiggs.D i (DerivativeLiteratureHiggs.h c a)) =
      (if c then -p i else p i) • ev p x y (DerivativeLiteratureHiggs.h c a) := by
  rw [DerivativeLiteratureHiggs.h,ColoredFourWaveEvaluation.first_value,
    ColoredFourWaveEvaluation.field_value]
  simp only [FourWavePolarization.linear,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  cases c <;> fin_cases s <;>
    simp [momenta,ColoredWavePairing.amplitudes,ColoredWavePairing.amplitudeInt,
      mul_ite]

theorem current (p : Fin 4 → ℂ) (x y : Fin 2) (i : Fin 4) :
    ev p x y (WeylHiggsCurrent.scalarCurrent i) =
      (2*p i) • ev p x y DerivativeLiteratureHiggs.rho := by
  simp only [WeylHiggsCurrent.scalarCurrent,map_sum,map_sub,map_mul,first]
  simp [Fin.sum_univ_two,DerivativeLiteratureHiggs.rho,map_add,map_mul,
    smul_add]
  module

theorem radius (p : Fin 4 → ℂ) (x y : Fin 2) :
    FourWaveEvaluation.coefficient ((ev p x y DerivativeLiteratureHiggs.rho)^2) =
      if x = y then 4 else 2 := by
  simp only [DerivativeLiteratureHiggs.rho,map_add,map_mul,
    DerivativeLiteratureHiggs.h,ColoredFourWaveEvaluation.field_value]
  rw [pow_two,add_mul,mul_add,mul_add]
  simp only [map_add,← mul_assoc,FourWavePolarization.coefficient_product]
  fin_cases x <;> fin_cases y <;>
    norm_num [FourWavePolarization.permanent,ColoredWavePairing.amplitudes,
      ColoredWavePairing.amplitudeInt]

theorem current_radius (p : Fin 4 → ℂ) (x y : Fin 2) (i : Fin 4) :
    ColoredFourWaveEvaluation.onJets (momenta p) (ColoredWavePairing.amplitudes x y)
      (WeylHiggsCurrent.scalarCurrent i * DerivativeLiteratureHiggs.rho) =
      (2*p i)*(if x = y then 4 else 2) := by
  change FourWaveEvaluation.coefficient (ev p x y
    (WeylHiggsCurrent.scalarCurrent i * DerivativeLiteratureHiggs.rho)) = _
  rw [map_mul,current,smul_mul_assoc,← pow_two,map_smul,radius]
  rfl

theorem current_scalar (p : Fin 4 → ℂ) (a b x y : Fin 2) (i : Fin 4)
    (q : DerivativeLiteratureHiggs.A) :
    probe p a b x y (DerivativeLiteratureMixed.current i * scalarEmbed q) =
      DerivativeLiteratureMixed.sigma i a b *
        ColoredFourWaveEvaluation.onJets (momenta p) (ColoredWavePairing.amplitudes x y) q := by
  fin_cases a <;> fin_cases b <;>
    simp [DerivativeLiteratureMixed.current,DerivativeLiteratureMixed.psi,MixedJetAlgebra.odd,
      MixedScalarInclusion.embed,Algebra.TensorProduct.includeRight_apply,
      Fin.sum_univ_succ,add_mul,smul_mul_assoc,Algebra.TensorProduct.tmul_mul_tmul,
      probe,MixedFourWaveEvaluation.probe_tmul,odd_pair]

theorem candidate (p : Fin 4 → ℂ) (a b x y : Fin 2) :
    probe p a b x y DerivativeLiteratureMixed.candidate =
      Complex.I * ∑ i : Fin 4, DerivativeLiteratureMixed.sigma i a b *
        ((2*p i)*(if x = y then 4 else 2)) := by
  unfold DerivativeLiteratureMixed.candidate
  rw [map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← WeylHiggsCurrent.higgs_current_dictionary,← WeylHiggsCurrent.rho_dictionary,
    mul_assoc,← map_mul,current_scalar,current_radius]

def nullVector : Fin 4 → ℂ := ![1,0,0,1]
theorem nullVector_null :
    (nullVector 0)^2-(nullVector 1)^2-(nullVector 2)^2-(nullVector 3)^2 = 0 := by
  norm_num [nullVector]

theorem nonzero_value : probe nullVector 0 0 0 0 DerivativeLiteratureMixed.candidate = 16*Complex.I := by
  rw [candidate]
  norm_num [Fin.sum_univ_succ,nullVector]
  norm_num [DerivativeLiteratureMixed.sigma,LorentzDirections.pauli,Pi.single_apply]
  ring

theorem candidate_not_relation : DerivativeLiteratureMixed.candidate ∉ input.relations := by
  intro h
  have hz := annihilates nullVector nullVector_null 0 0 0 0 h
  change probe nullVector 0 0 0 0 DerivativeLiteratureMixed.candidate = 0 at hz
  rw [nonzero_value] at hz
  exact (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) Complex.I_ne_zero) hz

end
end Physics.WeylHiggsWaveValues
