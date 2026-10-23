import Math.RepresentationTheory.Jets.JetFunctor

/-! Two different evaluations of derivative symbols: a single higher jet,
and products of first jets. Both commute with direction changes. -/
namespace Math.JetSymbolEvaluation
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections MvPolynomial

variable {I : Type*}

def linearized : Symbols I →ₗ[ℂ] ScalarJetAlgebra.Algebra Unit I :=
  JetLinear.linearForm.comp (ofSymbols ())

def firstJets : Symbols I →ₐ[ℂ] ScalarJetAlgebra.Algebra Unit I :=
  aeval (fun i => X ((), Finsupp.single i 1))

@[simp] theorem firstJets_X (i : I) : firstJets (X i) = X ((), Finsupp.single i 1) := by
  simp [firstJets]

theorem firstJets_linearForm (v : Direction I) :
    firstJets (JetDirections.linearForm v) = linearized (JetDirections.linearForm v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i c =>
    simp only [JetDirections.linearForm_single, map_smul, firstJets_X]
    congr 1
    change X ((), Finsupp.single i 1) = JetLinear.linearForm (ofSymbols () (X i))
    simp [MvPolynomial.X, JetLinear.linearForm]

theorem linearized_natural (f : Direction I →ₗ[ℂ] Direction I) (p : Symbols I) :
    JetFunctor.polynomialMap (jetMap (S := Unit) f) (linearized p) = linearized (symbolMap f p) := by
  change JetFunctor.polynomialMap (jetMap f) (JetLinear.linearForm (ofSymbols () p)) = _
  rw [JetFunctor.polynomialMap_linearForm]
  change JetLinear.linearForm (lift (symbolMap f).toLinearMap (ofSymbols () p)) = _
  rw [lift_ofSymbols]
  rfl

theorem firstJets_natural (f : Direction I →ₗ[ℂ] Direction I) (p : Symbols I) :
    JetFunctor.polynomialMap (jetMap (S := Unit) f) (firstJets p) = firstJets (symbolMap f p) := by
  have he : (JetFunctor.polynomialMap (jetMap (S := Unit) f)).comp firstJets =
      firstJets.comp (symbolMap f) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, firstJets_X, JetFunctor.polynomialMap_X,
      jetMap, lift_single, one_smul, symbolMap_X]
    rw [show monomial (Finsupp.single i 1) (1 : ℂ) = X i by rfl]
    change linearized (symbolMap f (X i)) = _
    rw [symbolMap_X, firstJets_linearForm]
  exact DFunLike.congr_fun he p

end
end Math.JetSymbolEvaluation
