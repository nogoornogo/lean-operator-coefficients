import Math.Algebra.Waves.FourWaveEvaluation
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar
import Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls

/-! A four-wave separator for the actual free scalar EOM/IBP quotient.
The fixed momenta are not a Lorentz-invariant coefficient. -/
namespace Physics.ScalarQuarticFourWitness
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM FourWaveEvaluation

def momenta : Fin 4 → Fin 4 → ℂ :=
  ![![1,0,0,1],![1,0,0,-1],![-1,-1,0,0],![-1,1,0,0]]

theorem conservation (i : Fin 4) : ∑ s : Fin 4, momenta s i = 0 := by
  fin_cases i <;> norm_num [momenta,Fin.sum_univ_succ]

abbrev ev := evaluation momenta
abbrev separator := onJets momenta

theorem field_value : ev field = X 0+X 1+X 2+X 3 := by
  simp [field,MasslessScalarEOM.field,jet,wave,Fin.sum_univ_succ,add_assoc]

theorem first_value (i : Fin 4) : ev (D i field) = ∑ s : Fin 4, momenta s i • X s := by
  rw [derivative,field_value]
  simp only [map_add,d_X]
  simp [Fin.sum_univ_succ,add_assoc]

theorem wave_zero : ev LorentzJetIBP.waveField = 0 := by
  rw [MasslessScalarEOM.waveField_formula]
  simp [jet,wave,momenta,Fin.sum_univ_succ,Finsupp.single_apply]
  ring

theorem ideal_zero {p : OffShell} (hp : p ∈ ideal 0) : ev p = 0 := by
  have hle : ideal 0 ≤ RingHom.ker ev.toRingHom := by
    apply DifferentialEquation.minimal
    · intro q hq
      change q ∈ {seed 0} at hq
      rw [Set.mem_singleton_iff] at hq
      rw [hq]
      simpa [seed] using wave_zero
    · intro i q hq
      change ev (D i q) = 0
      rw [derivative,show ev q = 0 from hq,map_zero]
  exact hle hp

theorem annihilates : (ScalarDerivativeInterface.scalar 0).relations ≤ separator.ker := by
  apply sup_le
  · intro p hp
    change coefficient (ev p) = 0
    rw [ideal_zero hp,map_zero]
  · rintro _ ⟨v,rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simpa only [map_add] using separator.ker.add_mem hu hv
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      exact divergence_zero momenta conservation i p

theorem kinetic_value : ev LorentzJetIBP.kinetic =
    4*X 0*X 1+4*X 2*X 3-2*(X 0+X 1)*(X 2+X 3) := by
  rw [DerivativeLiteratureScalar.kinetic_as_derivatives]
  simp only [map_sub,map_pow,first_value]
  norm_num [momenta,Fin.sum_univ_succ]
  ring

theorem four_value : separator DerivativeLiteratureScalar.fourDerivative = 48 := by
  change coefficient (ev (LorentzJetIBP.kinetic^2)) = 48
  rw [map_pow,kinetic_value]
  have he : (4*(X 0 : P)*X 1+4*X 2*X 3-2*(X 0+X 1)*(X 2+X 3))^2 =
      C (16:ℂ)*X 0^2*X 1^2+C (16:ℂ)*X 2^2*X 3^2+
      C (4:ℂ)*X 0^2*X 2^2+C (4:ℂ)*X 0^2*X 3^2+C (4:ℂ)*X 1^2*X 2^2+C (4:ℂ)*X 1^2*X 3^2+
      C (8:ℂ)*X 0^2*X 2*X 3+C (8:ℂ)*X 1^2*X 2*X 3+
      C (8:ℂ)*X 0*X 1*X 2^2+C (8:ℂ)*X 0*X 1*X 3^2+
      C (48:ℂ)*X 0*X 1*X 2*X 3-
      C (16:ℂ)*(X 0^2*X 1*X 2+X 0^2*X 1*X 3+X 0*X 1^2*X 2+X 0*X 1^2*X 3+
        X 0*X 2^2*X 3+X 0*X 2*X 3^2+X 1*X 2^2*X 3+X 1*X 2*X 3^2) := by
    norm_num only [map_ofNat]
    ring
  rw [he]
  simp only [coefficient,MvPolynomial.lcoeff_apply,X_pow_eq_monomial]
  simp only [X,mul_add,C_mul_monomial,monomial_mul_monomial]
  norm_num [squareFree,Fin.sum_univ_succ,coeff_monomial,Finsupp.ext_iff,Fin.forall_fin_succ]

theorem quotient_nonzero :
    (ScalarDerivativeInterface.scalar 0).projection DerivativeLiteratureScalar.fourDerivative ≠ 0 := by
  intro hz
  have hp := (Submodule.Quotient.mk_eq_zero _).mp hz
  have h := annihilates hp
  change separator DerivativeLiteratureScalar.fourDerivative = 0 at h
  rw [four_value] at h
  norm_num at h

theorem separator_before : separator ((D 0 field)^4) = 24 := by
  change coefficient (ev ((D 0 field)^4)) = 24
  rw [map_pow,first_value,coefficient_fourth]
  norm_num [momenta,Fin.prod_univ_succ]

theorem transformed_first : ev (offAction (LorentzFiniteControls.shear 1) (D 0 field)) =
    ∑ s : Fin 4, (![1,2,-1/2,-5/2] : Fin 4 → ℂ) s • X s := by
  rw [derivative_covariance,field_invariant,map_sum]
  simp only [map_smul,first_value,LorentzFiniteControls.real_direction]
  norm_num [LorentzFiniteControls.realRows,momenta,Fin.sum_univ_succ,
    smul_add,smul_sub,smul_smul]
  module

theorem separator_after : separator (offAction (LorentzFiniteControls.shear 1) ((D 0 field)^4)) = 60 := by
  change coefficient (ev (offAction (LorentzFiniteControls.shear 1) ((D 0 field)^4))) = 60
  rw [map_pow,map_pow,transformed_first,coefficient_fourth]
  norm_num [Fin.prod_univ_succ]

theorem separator_not_invariant :
    ¬ ∀ g p, separator (offAction g p) = separator p := by
  intro h
  have he := h (LorentzFiniteControls.shear 1) ((D 0 field)^4)
  rw [separator_after,separator_before] at he
  norm_num at he

end
end Physics.ScalarQuarticFourWitness
