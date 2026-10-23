import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInput

/-! Actual global invariance of the C5 density. Bosonic current and norm are
transported through the scalar inclusion; the Pauli current pairs with dual directions. -/
namespace Physics.WeylHiggsCurrent
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections PairedWeylKinetic
open scoped TensorProduct
open WeylHiggsInput

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem action_mul (g : Group) (p q : A) : action g (p*q) = action g p * action g q :=
  JetFunctor.mixedAction_mul jets bosons g p q

def scalarCurrent (i : Fin 4) : DerivativeLiteratureHiggs.A :=
  ∑ a : Fin 2,
    (DerivativeLiteratureHiggs.h true a * DerivativeLiteratureHiggs.D i (DerivativeLiteratureHiggs.h false a) -
    DerivativeLiteratureHiggs.D i (DerivativeLiteratureHiggs.h true a) * DerivativeLiteratureHiggs.h false a)

theorem scalar_current_internal (g : StandardSMGaugeTensor.GaugeGroup) (i : Fin 4) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g (scalarCurrent i) =
      scalarCurrent i := by
  have he : scalarCurrent i =
      PairedJetContractions.canonical (ι := Fin 2) (Finsupp.single i 1) 0 -
      PairedJetContractions.canonical (ι := Fin 2) 0 (Finsupp.single i 1) := by
    simp [scalarCurrent, PairedJetContractions.canonical_formula, Finset.sum_sub_distrib,
      DerivativeLiteratureHiggs.h, ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift,
      mul_comm]
  rw [he, map_sub, PairedJetContractions.canonical_invariant,
    PairedJetContractions.canonical_invariant]

theorem scalar_current_lorentz (g : LorentzDirections.Group) (i : Fin 4) :
    HiggsLagrangianInput.transport g (scalarCurrent i) =
      ∑ j : Fin 4, (LorentzDirections.direction g (Finsupp.single i 1)) j • scalarCurrent j := by
  simp only [scalarCurrent, map_sum, map_sub, map_mul,
    HiggsLagrangianInput.field_invariant, HiggsLagrangianInput.covariance,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum, smul_sub]

theorem scalar_current_covariant (g : Group) (i : Fin 4) :
    HiggsStandardInput.transport g (scalarCurrent i) =
      ∑ j : Fin 4, (directions g (Finsupp.single i 1)) j • scalarCurrent j := by
  rw [HiggsStandardInput.factorize, scalar_current_lorentz, map_sum]
  simp only [map_smul, scalar_current_internal]
  rfl

theorem psi_covariant (c : Bool) (g : Group) (a : Fin 2) :
    action g (psi c a) = StandardSMGaugeTensor.phase (charge c) g.1 •
      PairedWeylInput.action g.2 (psi c a) := by
  have h : PairedWeylInput.oddInc c (atOrder (I := Fin 4) 0 (Finsupp.single a 1)) =
      psi c a := by
    simp [atOrder, PairedWeylInput.oddInc, PairedWeylInput.jetInc_single,
      JetFunctor.oddVector_single, psi]
  rw [← h, WeylHiggsInput.oddInc_covariant, PairedWeylInput.oddInc_covariant]

theorem phases (g : StandardSMGaugeTensor.GaugeGroup) :
    StandardSMGaugeTensor.phase (charge false) g *
      StandardSMGaugeTensor.phase (charge true) g = 1 := by
  change (g.2.2 : ℂ) ^ (6:ℤ) * (g.2.2 : ℂ) ^ (-6:ℤ) = 1
  rw [← zpow_add₀ (Circle.coe_ne_zero _)]
  norm_num

theorem matrix_current_covariant (g : Group) (m : LorentzDirections.Mat) :
    action g (WeylCurrentCovariance.matrixCurrent m) =
      PairedWeylInput.action g.2 (WeylCurrentCovariance.matrixCurrent m) := by
  change action g (∑ a : Fin 2, ∑ b : Fin 2, m a b • (psi false a * psi true b)) =
    PairedWeylInput.action g.2 (∑ a : Fin 2, ∑ b : Fin 2, m a b • (psi false a * psi true b))
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [action_mul, psi_covariant, psi_covariant,
    smul_mul_assoc, mul_smul_comm, smul_smul, phases, one_smul]
  exact (JetFunctor.mixedAction_mul _ _ _ _ _).symm

theorem current_covariant (g : Group) (i : Fin 4) :
    action g (DerivativeLiteratureMixed.current i) =
      ∑ j : Fin 4, (LorentzDirections.vector g.2 (Pi.single i 1)) j •
        DerivativeLiteratureMixed.current j := by
  change action g (WeylCurrentCovariance.matrixCurrent _) = _
  rw [matrix_current_covariant]
  exact WeylCurrentCovariance.current_covariant g.2 i

theorem higgs_current_dictionary (i : Fin 4) : scalarEmbed (scalarCurrent i) =
    DerivativeLiteratureMixed.higgsCurrent i := by
  simp [scalarCurrent, Fin.sum_univ_two, scalarEmbed, MixedScalarInclusion.embed,
    Algebra.TensorProduct.includeRight_apply, DerivativeLiteratureHiggs.h,
    DerivativeLiteratureMixed.higgsCurrent, DerivativeLiteratureMixed.h,
    MixedJetAlgebra.even, MixedJetAlgebra.oddDerivative, ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift, TensorProduct.tmul_add,
    TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul]
  abel

theorem rho_dictionary : scalarEmbed DerivativeLiteratureHiggs.rho =
    DerivativeLiteratureMixed.rho := by
  simp [DerivativeLiteratureHiggs.rho, DerivativeLiteratureHiggs.h,
    DerivativeLiteratureMixed.rho, DerivativeLiteratureMixed.h, scalarEmbed,
    MixedScalarInclusion.embed, Algebra.TensorProduct.includeRight_apply,
    MixedJetAlgebra.even, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_add]

theorem rho_invariant (g : Group) : action g DerivativeLiteratureMixed.rho =
    DerivativeLiteratureMixed.rho := by
  rw [← rho_dictionary]
  change JetFunctor.mixedAction jets bosons g (MixedScalarInclusion.embed _) = _
  rw [MixedScalarInclusion.natural]
  have h : HiggsStandardInput.transport g DerivativeLiteratureHiggs.rho =
      DerivativeLiteratureHiggs.rho := by
    rw [HiggsStandardInput.factorize, HiggsLagrangianInput.rho_invariant,
      HiggsInternalSymmetry.radius_invariant]
  exact congrArg scalarEmbed h

theorem higgs_current_covariant (g : Group) (i : Fin 4) :
    action g (DerivativeLiteratureMixed.higgsCurrent i) =
      ∑ j : Fin 4, (directions g (Finsupp.single i 1)) j •
        DerivativeLiteratureMixed.higgsCurrent j := by
  rw [← higgs_current_dictionary]
  change JetFunctor.mixedAction jets bosons g (MixedScalarInclusion.embed _) = _
  rw [MixedScalarInclusion.natural]
  change scalarEmbed (HiggsStandardInput.transport g (scalarCurrent i)) = _
  rw [scalar_current_covariant, map_sum]
  simp only [map_smul, higgs_current_dictionary]

theorem inverse_pair (g : LorentzDirections.Group) (j k : Fin 4) :
    (∑ i : Fin 4, (LorentzDirections.direction g (Finsupp.single i 1)) k *
      (LorentzDirections.vector g (Pi.single i 1)) j) =
      if j = k then 1 else 0 := by
  simp_rw [LorentzDirections.direction_single]
  have h : LorentzDirections.vector g (LorentzDirections.vector g⁻¹ (Pi.single k 1)) =
      Pi.single k 1 := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    _ = (LorentzDirections.vector g
        (∑ i : Fin 4, (LorentzDirections.vector g⁻¹ (Pi.single k 1)) i • Pi.single i 1)) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := by rw [← WeylLinearEquation.expand, h]; simp [Pi.single_apply]

theorem contraction_invariant (g : Group) :
    action g (∑ i : Fin 4, DerivativeLiteratureMixed.current i *
      DerivativeLiteratureMixed.higgsCurrent i) =
      ∑ i : Fin 4, DerivativeLiteratureMixed.current i * DerivativeLiteratureMixed.higgsCurrent i := by
  simp only [map_sum, action_mul, current_covariant,
    higgs_current_covariant, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul,
    show directions g = LorentzDirections.direction g.2 from rfl]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [← Finset.sum_smul, inverse_pair]
  simp [ite_smul, Finset.sum_ite_eq']

theorem candidate_invariant (g : Group) :
    action g DerivativeLiteratureMixed.candidate = DerivativeLiteratureMixed.candidate := by
  have he : DerivativeLiteratureMixed.candidate = Complex.I •
      ((∑ i : Fin 4, DerivativeLiteratureMixed.current i *
        DerivativeLiteratureMixed.higgsCurrent i) * DerivativeLiteratureMixed.rho) := by
    simp only [DerivativeLiteratureMixed.candidate, Finset.sum_mul]
  rw [he, map_smul, action_mul, contraction_invariant, rho_invariant]

end
end Physics.WeylHiggsCurrent
