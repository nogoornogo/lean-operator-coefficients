import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalLift

/-! The actual mixed IBP relation joins the two internal Higgs coordinates.
Odd derivative terms vanish by the previously proved Weyl/Lorentz bound. -/
namespace Physics.WeylHiggsInternalLift
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
open WeylHiggsLorentzUpper
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def scalarProduct (b : Fin 4 → Label) : DerivativeLiteratureHiggs.A :=
  DerivativeLiteratureHiggs.h (b 0).1 (b 0).2 * DerivativeLiteratureHiggs.h (b 1).1 (b 1).2 *
    DerivativeLiteratureHiggs.h (b 2).1 (b 2).2 * DerivativeLiteratureHiggs.h (b 3).1 (b 3).2

theorem first_word_scalar (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    word c d b 0 (Finsupp.single i 1) (Finsupp.single a 1) (Finsupp.single e 1) =
      D i (psi c a)*psi d e*scalarEmbed (scalarProduct b) := by
  simp only [word,Math.MixedFirstJetTensor.word,Math.MixedFirstJetTensor.directional_single,
    one_smul,oddField_single,even_scalar,rest_scalar]
  simp only [scalarProduct,mul_assoc,← map_mul]

theorem second_word_scalar (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    word c d b 1 (Finsupp.single i 1) (Finsupp.single a 1) (Finsupp.single e 1) =
      psi c a*D i (psi d e)*scalarEmbed (scalarProduct b) := by
  simp only [word,Math.MixedFirstJetTensor.word,Math.MixedFirstJetTensor.directional_single,
    one_smul,oddField_single,even_scalar,rest_scalar]
  simp only [scalarProduct,mul_assoc,← map_mul]

theorem derivative_zero (f : A →ₗ[ℂ] ℂ) (hRel : input.relations ≤ f.ker) (i : Fin 4) (p : A) :
    f (D i p) = 0 :=
  hRel (Submodule.mem_sup_right ⟨Finsupp.single i p,VariationalIBP.divergence_single D i p⟩)

theorem scalar_product_zero (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker)
    (b : Fin 4 → Label) :
    scalarFunctional f (DerivativeLiteratureHiggs.D 0 (scalarProduct b)) = 0 := by
  have h0 := first_zero f h hRel false true b 0 0 0
  rw [component_word,first_word_scalar] at h0
  have h1 := second_zero f h hRel false true b 0 0 0
  rw [component_word,second_word_scalar] at h1
  have hz := derivative_zero f hRel 0 (psi false 0*psi true 0*scalarEmbed (scalarProduct b))
  rw [MixedJetAlgebra.totalDerivative_mul,MixedJetAlgebra.totalDerivative_mul,
    add_mul,MixedScalarInclusion.derivative,map_add,map_add,h0,h1,zero_add,zero_add] at hz
  exact hz

theorem derivative_four (i : Fin 4) (a b c d : DerivativeLiteratureHiggs.A) :
    DerivativeLiteratureHiggs.D i (a*b*c*d) =
      DerivativeLiteratureHiggs.D i a*b*c*d+DerivativeLiteratureHiggs.D i b*a*c*d+
        DerivativeLiteratureHiggs.D i c*a*b*d+DerivativeLiteratureHiggs.D i d*a*b*c := by
  simp only [ScalarJetAlgebra.totalDerivative_mul]
  ring

theorem radial_relation (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker) :
    HiggsFirstInternal.K (scalarFunctional f) 0 0 2 2+
      HiggsFirstInternal.K (scalarFunctional f) 2 0 0 2 = 0 := by
  have hz := scalar_product_zero f h hRel (labels 0 0 2 2)
  change scalarFunctional f (DerivativeLiteratureHiggs.D 0
    (HiggsQuarticFourInternalControls.field 0*HiggsQuarticFourInternalControls.field 0*
      HiggsQuarticFourInternalControls.field 2*HiggsQuarticFourInternalControls.field 2)) = 0 at hz
  rw [derivative_four] at hz
  simp only [map_add,← HiggsFirstInternal.K_apply] at hz
  linear_combination (1/2 : ℂ)*hz

end
end Physics.WeylHiggsInternalLift
