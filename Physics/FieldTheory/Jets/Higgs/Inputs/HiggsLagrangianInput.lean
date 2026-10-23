import Math.RepresentationTheory.Lagrangian.HiggsLagrangianInput
import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP

/-! Actual Lorentz transport of the generated gaugeless Higgs equations.
Each component is a scalar; internal weak/conjugation data are separate. -/
namespace Physics.HiggsLagrangianInput
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs JetDirections

def action : Representation ℂ LorentzDirections.Group A :=
  JetFunctor.polynomialAction (jetAction (S := Label) LorentzDirections.direction)
def transport (g : LorentzDirections.Group) : A →ₐ[ℂ] A :=
  JetFunctor.polynomialMap (jetMap (S := Label) (LorentzDirections.direction g))

def linearSymbol (j : Label) : Symbols (Fin 4) →ₗ[ℂ] A :=
  JetLinear.linearForm.comp (ofSymbols j)

theorem linearSymbol_natural (g : LorentzDirections.Group) (j : Label)
    (p : Symbols (Fin 4)) : transport g (linearSymbol j p) =
      linearSymbol j (symbolMap (LorentzDirections.direction g) p) := by
  change JetFunctor.polynomialMap _ (JetLinear.linearForm (ofSymbols j p)) = _
  rw [JetFunctor.polynomialMap_linearForm]
  change JetLinear.linearForm (lift _ (ofSymbols j p)) = _
  rw [lift_ofSymbols]
  rfl

theorem linearSymbol_one (j : Label) : linearSymbol j 1 = h j.1 j.2 := by
  change JetLinear.linearForm (ofSymbols j 1) = _
  rw [show (1 : Symbols (Fin 4)) = MvPolynomial.monomial 0 1 by simp,
    ofSymbols_monomial]
  simp [JetLinear.linearForm,h]

theorem field_invariant (g : LorentzDirections.Group) (c : Bool) (i : Fin 2) :
    transport g (h c i) = h c i := by
  rw [← linearSymbol_one (c,i),linearSymbol_natural,map_one]

theorem rho_invariant (g : LorentzDirections.Group) : transport g rho = rho := by
  simp only [rho,map_add,map_mul,field_invariant]

theorem linearSymbol_wave (j : Label) :
    linearSymbol j LorentzDirections.wave = box (h j.1 j.2) := by
  simp [linearSymbol,LorentzDirections.wave,MvPolynomial.X_pow_eq_monomial,
    JetLinear.linearForm,box,h,ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift,← Finsupp.single_add]

theorem wave_invariant (g : LorentzDirections.Group) (j : Label) :
    transport g (box (h j.1 j.2)) = box (h j.1 j.2) := by
  rw [← linearSymbol_wave,linearSymbol_natural,LorentzDirections.wave_invariant]

theorem seed_invariant (a b : ℂ) (g : LorentzDirections.Group) (j : Label) :
    transport g (seed a b j) = seed a b j := by
  simp only [seed,map_add,map_mul,MvPolynomial.algHom_C,MvPolynomial.algebraMap_eq,rho_invariant,field_invariant,
    wave_invariant]

theorem covariance (g : LorentzDirections.Group) (i : Fin 4) (p : A) :
    transport g (D i p) = ∑ k, (LorentzDirections.direction g (Finsupp.single i 1)) k •
      D k (transport g p) := by
  exact JetFunctor.polynomial_covariant
    (jetAction (S := Label) LorentzDirections.direction) g i _
    (jetMap_covariant (LorentzDirections.direction g) i) p

theorem ideal_stable (a b : ℂ) (g : LorentzDirections.Group) :
    ∀ p ∈ DifferentialEquation.ideal D (seeds a b),
      transport g p ∈ DifferentialEquation.ideal D (seeds a b) := by
  apply DifferentialEquation.map_stable
  · rintro p ⟨j,rfl⟩
    rw [seed_invariant]
    exact DifferentialEquation.seed_mem _ _ ⟨j,rfl⟩
  · intro i p hp
    rw [covariance]
    exact Submodule.sum_mem _ (fun k _ =>
      (DifferentialEquation.relations D (seeds a b)).smul_mem _
        (DifferentialEquation.stable D _ k hp))

theorem stable (a b : ℂ) : ∀ g, DifferentialEquation.combined D (seeds a b) ≤
    (DifferentialEquation.combined D (seeds a b)).comap (action g) := by
  intro g
  exact DifferentialEquation.combined_map_stable D _ (transport g) (ideal_stable a b g)
    (fun i k => (LorentzDirections.direction g (Finsupp.single i 1)) k) (covariance g)

theorem generated_stable (a b : ℂ) : ∀ g,
    DifferentialEquation.combined D (Math.HiggsLagrangianInput.density a b).scalarSeeds ≤
      (DifferentialEquation.combined D (Math.HiggsLagrangianInput.density a b).scalarSeeds).comap
        (action g) := by
  rw [Math.HiggsLagrangianInput.generated_relations]
  exact stable a b

def input (a b : ℂ) :=
  (Math.HiggsLagrangianInput.density a b).scalarInput action (generated_stable a b)

theorem extraction (a b : ℂ) (f : (input a b).Coefficient) (p : A) :
    (input a b).coefficientEquiv f ((input a b).projection p) = f.val p := rfl

end
end Physics.HiggsLagrangianInput
