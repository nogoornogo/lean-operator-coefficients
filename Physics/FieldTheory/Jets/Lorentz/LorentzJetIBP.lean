import Physics.FieldTheory.Jets.Lorentz.LorentzDirections
import Math.Algebra.Jets.JetSymbolEvaluation
import Math.RepresentationTheory.Jets.DirectionalJetIBP

/-! Actual scalar metric contractions, Weyl derivative symbols and Lorentz IBP.
Derivative symbols carry the dual four-vector action, in signature (+---). -/
namespace Physics.LorentzJetIBP
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections

abbrev Group := LorentzDirections.Group

def scalarField : Representation ℂ Group (JetLinear.Field Unit) :=
  Representation.trivial ℂ Group (JetLinear.Field Unit)

def spinorBasis : JetLinear.Field (Fin 2) ≃ₗ[ℂ] WeylSpinor.Space :=
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2)

def weyl (right : Bool) : Representation ℂ Group (JetLinear.Field (Fin 2)) :=
  spinorBasis.symm.conjRingEquiv.toMonoidHom.comp (if right then WeylSpinor.right else WeylSpinor.left)

theorem weyl_basis (right : Bool) (g : Group) (v : JetLinear.Field (Fin 2)) :
    spinorBasis (weyl right g v) = (if right then WeylSpinor.right else WeylSpinor.left) g (spinorBasis v) := by
  change spinorBasis (spinorBasis.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.symm_symm]
  rfl

theorem weyl_derivative (right : Bool) (g : Group) (i : Fin 4) (v : JetLinear.Field (Fin 2)) :
    combined (weyl right) LorentzDirections.direction g (JetLinear.shift i (atOrder 0 v)) =
      ∑ j, (LorentzDirections.direction g (Finsupp.single i 1)) j •
        JetLinear.shift j (atOrder 0 (weyl right g v)) := by
  rw [combined_covariant, combined_zero]

def scalarAction := JetFunctor.polynomialAction (combined scalarField LorentzDirections.direction)

def kinetic : ScalarJetAlgebra.Algebra Unit (Fin 4) := JetSymbolEvaluation.firstJets LorentzDirections.wave
def waveField : ScalarJetAlgebra.Algebra Unit (Fin 4) := JetSymbolEvaluation.linearized LorentzDirections.wave

theorem kinetic_formula : kinetic =
    MvPolynomial.X ((), Finsupp.single (0 : Fin 4) 1) ^ 2 -
    MvPolynomial.X ((), Finsupp.single (1 : Fin 4) 1) ^ 2 -
    MvPolynomial.X ((), Finsupp.single (2 : Fin 4) 1) ^ 2 -
    MvPolynomial.X ((), Finsupp.single (3 : Fin 4) 1) ^ 2 := by
  simp [kinetic, LorentzDirections.wave]

theorem kinetic_invariant (g : Group) : scalarAction g kinetic = kinetic := by
  change JetFunctor.polynomialMap (combined scalarField LorentzDirections.direction g)
    (JetSymbolEvaluation.firstJets LorentzDirections.wave) = _
  rw [show combined scalarField LorentzDirections.direction g = jetMap (S := Unit) (LorentzDirections.direction g)
    from combined_trivial LorentzDirections.direction g,
    JetSymbolEvaluation.firstJets_natural, LorentzDirections.wave_invariant]
  rfl

theorem waveField_invariant (g : Group) : scalarAction g waveField = waveField := by
  change JetFunctor.polynomialMap (combined scalarField LorentzDirections.direction g)
    (JetSymbolEvaluation.linearized LorentzDirections.wave) = _
  rw [show combined scalarField LorentzDirections.direction g = jetMap (S := Unit) (LorentzDirections.direction g)
    from combined_trivial LorentzDirections.direction g,
    JetSymbolEvaluation.linearized_natural, LorentzDirections.wave_invariant]
  rfl

def scalarCoefficientEquiv (n d : ℕ) :=
  DirectionalJetIBP.scalarCoefficientEquiv LorentzDirections.direction scalarField n d

def weylMixedCoefficientEquiv (right : Bool) (n m d : ℕ) :=
  DirectionalJetIBP.mixedCoefficientEquiv LorentzDirections.direction (weyl right) scalarField n m d

def weylSourceEquiv (right : Bool) (n m d : ℕ) :=
  DirectionalJetIBP.mixedSourceEquiv LorentzDirections.direction (weyl right) scalarField n m d

end
end Physics.LorentzJetIBP
