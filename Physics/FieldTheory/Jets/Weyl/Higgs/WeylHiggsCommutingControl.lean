import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInput

/-! A commuting domain-valued algebra substitution kills all odd jets.
Scalar-wave algebra substitutions cannot separate a fermionic current. -/
namespace Physics.WeylHiggsCommutingControl
set_option autoImplicit false
noncomputable section
open Math PairedWeylKinetic
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]

theorem odd_zero (f : A →ₐ[ℂ] R) (j : ScalarJetAlgebra.Index Label (Fin 4)) :
    f (MixedJetAlgebra.odd (B := Label) j) = 0 := by
  have h : f (MixedJetAlgebra.odd (B := Label) j) ^ 2 = 0 := by
    rw [← map_pow, MixedJetAlgebra.odd_square, map_zero]
  exact eq_zero_of_pow_eq_zero h

theorem current_zero (f : A →ₐ[ℂ] R) (i : Fin 4) :
    f (DerivativeLiteratureMixed.current i) = 0 := by
  simp [DerivativeLiteratureMixed.current, DerivativeLiteratureMixed.psi, odd_zero]

theorem candidate_zero (f : A →ₐ[ℂ] R) : f DerivativeLiteratureMixed.candidate = 0 := by
  simp only [DerivativeLiteratureMixed.candidate, map_smul, map_sum, map_mul,
    current_zero, zero_mul, Finset.sum_const_zero, smul_zero]

end
end Physics.WeylHiggsCommutingControl
