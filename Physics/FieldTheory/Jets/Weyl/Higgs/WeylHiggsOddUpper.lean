import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLorentzUpper
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstSource

/-! Both odd derivative allocations vanish by actual Weyl equations and
Lorentz invariance. The swap retains the Grassmann sign. -/
namespace Physics.WeylHiggsLorentzUpper
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput WeylHiggsFirstTensor
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

theorem odd_first_swap (c d : Bool) (a e : Fin 2) (i : Fin 4) :
    psi c a * D i (psi d e) = -(D i (psi d e) * psi c a) := by
  change MixedJetAlgebra.odd ((c,a),0) *
    MixedJetAlgebra.totalDerivative i (MixedJetAlgebra.odd ((d,e),0)) =
      -(MixedJetAlgebra.totalDerivative i (MixedJetAlgebra.odd ((d,e),0)) * MixedJetAlgebra.odd ((c,a),0))
  rw [MixedJetAlgebra.totalDerivative_odd]
  have hs := MixedJetParity.odd_slide (I := Fin 4) ((c,a),0)
    (MixedJetAlgebra.odd (B := Label) (ScalarJetAlgebra.shift i ((d,e),0)))
  rw [MixedJetParity.involute_odd] at hs
  exact hs.trans (neg_mul _ _)

theorem component_swap_second (f : A →ₗ[ℂ] ℂ) (c d : Bool) (b : Fin 4 → Label)
    (a e : Fin 2) (i : Fin 4) :
    C f c d b 1 a e i = -C f d c b 0 e a i := by
  rw [component_word,component_word]
  simp only [word,Math.MixedFirstJetTensor.word,Math.MixedFirstJetTensor.directional_single,
    one_smul,oddField_single]
  rw [odd_first_swap,neg_mul,neg_mul,map_neg]

theorem second_zero (f : A →ₗ[ℂ] ℂ)
    (h : ∀ g p, p ∈ V → f (action g p) = f p) (hRel : input.relations ≤ f.ker)
    (c d : Bool) (b : Fin 4 → Label) (a e : Fin 2) (i : Fin 4) :
    C f c d b 1 a e i = 0 := by
  rw [component_swap_second,first_zero f h hRel,neg_zero]

end
end Physics.WeylHiggsLorentzUpper
