import Math.RepresentationTheory.Jets.JetFunctor

/-! Exact removal of positive jets commutes with every linear direction map.
This supplies actual full-relation functionals, rather than raw jet probes. -/
namespace Math.JetConstantProjection
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open JetDirections JetLinear MvPolynomial
variable {S I : Type*}

def augmentation : Symbols I →ₐ[ℂ] ℂ where
  toRingHom := constantCoeff
  commutes' c := by simp

theorem augmentation_linearForm (v : Direction I) :
    augmentation (JetDirections.linearForm v) = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw,add_zero]
  | single i c => simp [JetDirections.linearForm_single,augmentation]

theorem augmentation_symbolMap (f : Direction I →ₗ[ℂ] Direction I) (p : Symbols I) :
    augmentation (symbolMap f p) = augmentation p := by
  have he : augmentation.comp (symbolMap f) = augmentation := by
    apply MvPolynomial.algHom_ext
    intro i
    change augmentation (symbolMap f (X i)) = augmentation (X i)
    rw [symbolMap_X,augmentation_linearForm]
    simp [augmentation]
  exact DFunLike.congr_fun he p

def constantJets : ScalarJetAlgebra.Algebra S I →ₐ[ℂ] MvPolynomial S ℂ := by
  classical
  exact aeval (fun j => if j.2 = 0 then X j.1 else 0)

theorem constantJets_X (j : ScalarJetAlgebra.Index S I) :
    constantJets (X j) = if j.2 = 0 then X j.1 else 0 := by
  classical
  simp [constantJets]

def residue : Jet S I →ₗ[ℂ] MvPolynomial S ℂ := by
  classical
  exact Finsupp.linearCombination ℂ (fun j => if j.2 = 0 then X j.1 else 0)

theorem constantJets_linearForm (v : Jet S I) :
    constantJets (JetLinear.linearForm v) = residue v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c =>
    simp [JetLinear.linearForm,residue,constantJets_X]

theorem residue_ofSymbols (s : S) (p : Symbols I) :
    residue (ofSymbols s p) = p.coeff 0 • X s := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [ofSymbols_monomial]
    by_cases ha : a = 0 <;> simp [residue,coeff_monomial,ha]
  | add p q hp hq => simpa [add_smul] using congrArg₂ (·+·) hp hq

theorem constantJets_direction (f : Direction I →ₗ[ℂ] Direction I)
    (p : ScalarJetAlgebra.Algebra S I) :
    constantJets (JetFunctor.polynomialMap (jetMap f) p) = constantJets p := by
  classical
  have he : constantJets.comp (JetFunctor.polynomialMap (jetMap f)) =
      (constantJets : ScalarJetAlgebra.Algebra S I →ₐ[ℂ] MvPolynomial S ℂ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨s,a⟩
    change constantJets (JetFunctor.polynomialMap (jetMap f) (X (s,a))) = _
    rw [JetFunctor.polynomialMap_X,constantJets_linearForm]
    change residue (lift (symbolMap f).toLinearMap (Finsupp.single (s,a) 1)) = _
    rw [lift_single,one_smul,residue_ofSymbols]
    have hc := augmentation_symbolMap f (monomial a 1)
    change (symbolMap f (monomial a 1)).coeff 0 = (monomial a 1).coeff 0 at hc
    change (symbolMap f (monomial a 1)).coeff 0 • X s = _
    rw [hc,constantJets_X]
    by_cases ha : a = 0 <;> simp [coeff_monomial,ha]
  exact DFunLike.congr_fun he p

theorem constantJets_shift (i : I) (j : ScalarJetAlgebra.Index S I) :
    constantJets (X (ScalarJetAlgebra.shift i j)) = 0 := by
  classical
  have hz : j.2+Finsupp.single i 1 ≠ 0 := by
    intro he
    have hi := congrArg (fun a : I →₀ ℕ => a i) he
    simp at hi
  simp [constantJets_X,ScalarJetAlgebra.shift,hz]

theorem constantJets_derivative (i : I) (p : ScalarJetAlgebra.Algebra S I) :
    constantJets (ScalarJetAlgebra.totalDerivative i p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | mul_X p j hp =>
    rw [ScalarJetAlgebra.totalDerivative_mul,ScalarJetAlgebra.totalDerivative_X,
      map_add,map_mul,map_mul,hp,constantJets_shift]
    simp

end
end Math.JetConstantProjection
