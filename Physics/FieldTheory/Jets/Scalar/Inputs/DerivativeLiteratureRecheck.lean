import Math.RepresentationTheory.Jets.FiniteDerivativeScalarControl
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar

/-! Renewed bounded literature consumers of the proved foundations.
The paper identities motivate the tests; no paper count is a premise. -/
namespace Physics.DerivativeLiteratureRecheck
set_option autoImplicit false
noncomputable section
open Math

namespace C1
open FiniteDerivativeScalarControl

/-- An admitted off-shell coefficient, constructed from the certified rows. -/
def offCoefficient (c : ℂ) : DerivativeLiteratureScalar.offInput.Coefficient :=
  off.decode ⟨![c,-c],(off_rows_iff _).mpr (by simp)⟩

theorem off_values (c : ℂ) :
    (offCoefficient c).val ScalarJetQuadratic.first = c ∧
    (offCoefficient c).val ScalarJetQuadratic.second = -c := by
  exact ⟨assemble_first _,assemble_second _⟩

theorem on_forbidden (f : Math.DerivativeLiteratureScalar.onInput.Coefficient) : f = 0 := by
  apply on.equivalence.injective
  rw [map_zero]
  exact on_rows_zero _
end C1

namespace C2
theorem certified_controls :
    Module.finrank ℂ (ScalarZeroDerivativeCertificate.Image 4) = 1 ∧
    DerivativeLiteratureScalar.freeInput.projection
      DerivativeLiteratureScalar.twoDerivative = 0 ∧
    ∀ g : LorentzDirections.Group, PolynomialScalarEOM.offAction g
      DerivativeLiteratureScalar.fourDerivative = DerivativeLiteratureScalar.fourDerivative :=
  ⟨ScalarZeroDerivativeCertificate.four_scalar_dimension,
    DerivativeLiteratureScalar.two_projection_zero,DerivativeLiteratureScalar.four_invariant⟩
end C2

namespace C3
open Math.DerivativeLiteratureHiggs

/-- Eq. (2.1) of 1008.4884v3, with gauge and Yukawa couplings set to zero.
`m2` denotes the signed mass-squared parameter, with no positivity premise. -/
abbrev input (m2 lambda : ℝ) := HiggsStandardInput.input (-(m2:ℂ)) (lambda:ℂ)

theorem density (m2 lambda : ℝ) :
    (Math.HiggsLagrangianInput.density (-(m2:ℂ)) (lambda:ℂ)).scalarEval =
      kinetic+(m2:ℂ) • rho-((lambda:ℂ)/2) • rho^2 := by
  rw [Math.HiggsLagrangianInput.density_eval]
  simp only [neg_smul,sub_neg_eq_add]

/-- The cross-field-count relation holds in the full generated quotient. -/
theorem quotient_relation (m2 lambda : ℝ) :
    (input m2 lambda).projection
      (redundant-(1/2:ℂ) • qBox+(m2:ℂ) • rho^2-(lambda:ℂ) • rho^3) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change _ ∈ DifferentialEquation.combined D
    (Math.HiggsLagrangianInput.density (-(m2:ℂ)) (lambda:ℂ)).scalarSeeds
  rw [Math.HiggsLagrangianInput.generated_relations]
  have hm := Submodule.smul_mem
    (DifferentialEquation.combined D (seeds (-(m2:ℂ)) (lambda:ℂ)))
    (1/2:ℂ) (reduction_mem (-(m2:ℂ)) (lambda:ℂ))
  have hc : (MvPolynomial.C (1/2:ℂ) : A)*2 = 1 := by
    have he : (1/2:ℂ)*2 = 1 := by norm_num
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (MvPolynomial.C (σ := ScalarJetAlgebra.Index Label (Fin 4))) he
  convert hm using 1
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_neg]
  norm_num only [map_ofNat]
  linear_combination -(redundant+MvPolynomial.C (m2:ℂ)*rho^2-
    MvPolynomial.C (lambda:ℂ)*rho^3)*hc

/-- The exact signed version of the schematic class reduction (5.3). -/
theorem coefficient_relation (m2 lambda : ℝ) (f : (input m2 lambda).Coefficient) :
    f.val redundant = (1/2:ℂ)*f.val qBox-(m2:ℂ)*f.val (rho^2)+
      (lambda:ℂ)*f.val (rho^3) := by
  simpa only [neg_mul,sub_eq_add_neg] using
    HiggsStandardInput.higgs_relation (-(m2:ℂ)) (lambda:ℂ) f

/-- Dropping the potential contribution is valid exactly when its value vanishes. -/
theorem derivative_only_iff (m2 lambda : ℝ) (f : (input m2 lambda).Coefficient) :
    f.val redundant = (1/2:ℂ)*f.val qBox ↔
      -(m2:ℂ)*f.val (rho^2)+(lambda:ℂ)*f.val (rho^3) = 0 := by
  have h := coefficient_relation m2 lambda f
  constructor <;> intro hz
  · linear_combination hz-h
  · linear_combination h+hz
end C3

namespace C4
open Math.DerivativeLiteratureHiggs

def divergenceWitness : A :=
  D 0 (h true 0*first false 0 0*first true 0 0*first false 0 0)

theorem witness_zero : (HiggsStandardInput.input 0 0).projection divergenceWitness = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change _ ∈ DifferentialEquation.combined D _
  exact Submodule.mem_sup_right
    ⟨Finsupp.single 0 _,Finsupp.lsum_single ℂ _ _ _⟩

/-- The old raw separator cannot be used as a coefficient on the new input. -/
theorem raw_probe_rejected : ¬∃ f : (HiggsStandardInput.input 0 0).Coefficient,
    ∀ p, f.val p = probe 0 p := by
  rintro ⟨f,hf⟩
  have hz : f.val divergenceWitness = 0 := by
    rw [← (HiggsStandardInput.input 0 0).extraction f divergenceWitness,witness_zero,map_zero]
  rw [hf] at hz
  have hp : probe 0 divergenceWitness = 1 := probe_not_ibp
  exact one_ne_zero (hp.symm.trans hz)

theorem raw_independence (a b c : ℂ) (h : a • q1+b • q2+c • q3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := raw_independent a b c h
end C4

namespace C5
open DerivativeLiteratureMixed
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def currentDivergence : A := ∑ i, D i (current i)

/-- Pauli signs and odd order checked before using either equation family. -/
theorem divergence_identity : currentDivergence =
    PairedWeylKinetic.left 0*psi true 0+PairedWeylKinetic.left 1*psi true 1+
      (psi false 0*PairedWeylKinetic.right 0+psi false 1*PairedWeylKinetic.right 1) := by
  simp [currentDivergence,current,sigma,LorentzDirections.pauli,Fin.sum_univ_succ,
    PairedWeylKinetic.left,PairedWeylKinetic.right,
    show PairedWeylKinetic.psi = psi from rfl,
    MixedJetAlgebra.totalDerivative_mul]
  simp only [add_mul,sub_mul,mul_add,mul_sub,smul_mul_assoc,mul_smul_comm]
  module

theorem divergence_eom : currentDivergence ∈
    TwoSidedDifferential.relations D PairedWeylKinetic.seeds := by
  rw [divergence_identity]
  have hl (a : Fin 2) : PairedWeylKinetic.left a ∈
      TwoSidedDifferential.relations D PairedWeylKinetic.seeds :=
    TwoSidedDifferential.seed_mem _ _
      ⟨(false,a),PairedWeylKinetic.seed_false a⟩
  have hr (a : Fin 2) : PairedWeylKinetic.right a ∈
      TwoSidedDifferential.relations D PairedWeylKinetic.seeds :=
    TwoSidedDifferential.seed_mem _ _
      ⟨(true,a),PairedWeylKinetic.seed_true a⟩
  exact Submodule.add_mem _
    (Submodule.add_mem _ (TwoSidedDifferential.right_mem _ _ _ (hl 0))
      (TwoSidedDifferential.right_mem _ _ _ (hl 1)))
    (Submodule.add_mem _ (TwoSidedDifferential.left_mem _ _ _ (hr 0))
      (TwoSidedDifferential.left_mem _ _ _ (hr 1)))

theorem conserved_products (f : PairedWeylInput.generated.Coefficient) (p q : A) :
    f.val (p*currentDivergence*q) = 0 := by
  apply f.property
  change _ ∈ PairedWeylKinetic.density.relations
  rw [PairedWeylKinetic.relations_equal]
  exact Submodule.mem_sup_left (TwoSidedDifferential.right_mem _ _ _
    (TwoSidedDifferential.left_mem _ _ _ divergence_eom))

/-- The symmetric derivative current is redundant; this does not test the
nonzero class of the bidirectional candidate in (4.24). -/
theorem symmetric_current_zero (f : PairedWeylInput.generated.Coefficient) (p : A) :
    f.val (∑ i, current i*D i p) = 0 := by
  have hi (i : Fin 4) : f.val (current i*D i p) = -f.val (D i (current i)*p) :=
    PairedWeylInput.current_ibp (PairedWeylInput.toDirect f) i _ _
  have he : f.val (∑ i, current i*D i p) = -f.val (currentDivergence*p) := by
    simp only [map_sum,hi,Finset.sum_neg_distrib,currentDivergence,Finset.sum_mul]
  rw [he]
  have hz := conserved_products f 1 p
  simpa only [one_mul,neg_zero] using congrArg Neg.neg hz

theorem reorder_value (f : PairedWeylInput.generated.Coefficient) (i : Fin 4) :
    f.val (current i*higgsCurrent i*rho) =
      -f.val (reversed i*higgsCurrent i*rho) := by
  rw [current_reorder,neg_mul,neg_mul,map_neg]
end C5

namespace C6
open DerivativeLiteratureScalar

theorem generated_first_zero (g : ℂ) (f : (quarticInput g).Coefficient) :
    f.val ((T (quarticDensity g).scalarEval).coeff 1) = 0 := by
  rw [← (quarticInput g).extraction f,helper_first_onShell,map_zero]

theorem second_order_control :
    (T (ScalarFirstVariation.lagrangian 0)).coeff 2 =
      (9/2:ℂ) • (PolynomialScalarEOM.field^4*LorentzJetIBP.kinetic) ∧
    (T (ScalarFirstVariation.lagrangian 0)).coeff 2 ≠ 0 := by
  constructor
  · simpa only [mul_zero,zero_mul,zero_div,zero_smul,sub_zero] using substitution_second 0
  · exact second_raw_nonzero
end C6

end
end Physics.DerivativeLiteratureRecheck
