import Physics.StandardModel.Operators.DipolePolynomialAutomation
import Physics.StandardModel.Operators.DipoleCouplingControls

open Math

/-! End-to-end automatic certificates; all models here are algebraic controls. -/
namespace GUT.DipolePolynomialAutomationExamples
set_option autoImplicit false
noncomputable section
open Representation DipoleControls DipoleModelInterface MvPolynomial

def scalarBasis : Module.Basis Unit ℂ ℂ := Module.Basis.singleton Unit ℂ
def incomingCoordinates (_ : Unit) : MvPolynomial Unit ℂ := (X ())^2
def outgoingCoordinates (_ : Unit) : MvPolynomial Unit ℂ := X ()

def cubic := DipolePolynomialAutomation.register flavor flavor flavor
  (DipoleCouplingControls.model 1) scalarBasis scalarBasis incomingCoordinates outgoingCoordinates
  (fun _ => Set.univ) mu electron

def cubicCertificate := DipolePolynomialAutomation.certificate flavor flavor flavor
  (DipoleCouplingControls.model 1) scalarBasis scalarBasis incomingCoordinates outgoingCoordinates
  (fun _ => Set.univ) mu electron (fun _ => Set.infinite_univ)

theorem cubic_selected (x : Unit → ℂ) : cubic.observe x = ((x ())^3,0) := by
  change DipoleFlavorSelection.selector flavor flavor mu electron
    (DipoleCouplingModel.generation flavor flavor flavor (DipoleCouplingControls.model 1)
      (PolynomialBasisCoordinates.evaluate scalarBasis incomingCoordinates x)
      (PolynomialBasisCoordinates.evaluate scalarBasis outgoingCoordinates x)) = _
  rw [DipoleCouplingControls.selected]
  simp [PolynomialBasisCoordinates.evaluate, scalarBasis, incomingCoordinates,
    outgoingCoordinates, pow_succ]

theorem cubic_realized : ∃ x, cubic.NonzeroInput x := by
  apply cubicCertificate.exists_nonzero_iff.mpr
  refine ⟨Finsupp.single () 3, ?_⟩
  have hw : ∀ i : Unit × Unit,
      PolynomialBasisCoordinates.weights incomingCoordinates outgoingCoordinates i = (X ())^3 := by
    intro i
    simp only [PolynomialBasisCoordinates.weights, incomingCoordinates, outgoingCoordinates]
    ring
  simp [PolynomialCertificate.grouped, cubicCertificate, DipolePolynomialAutomation.certificate,
    DipolePolynomialAutomation.register, ofCouplings, ofResidual,
    BilinearSelectedPaths.paths, DipoleCouplingModel.residual, DipoleCouplingControls.model,
    scalarBasis, hw, MvPolynomial.X_pow_eq_monomial]

def explicitGeneration (x : Unit → ℂ) : DipoleFlavorSelection.Coefficients flavor flavor :=
  DipoleCouplingModel.generation flavor flavor flavor (DipoleCouplingControls.model 1)
    ((x ())^2) (x ())

theorem correspondence : ∀ x ∈ cubic.admissible,
    (DipoleSMCoefficient.equiv flavor flavor) (explicitGeneration x) = cubic.residual x := by
  intro x _
  simp [explicitGeneration, cubic, DipolePolynomialAutomation.register, ofCouplings, ofResidual,
    PolynomialBasisCoordinates.evaluate, scalarBasis, incomingCoordinates, outgoingCoordinates]

def externalCertificate := cubicCertificate.withCoefficients explicitGeneration correspondence

theorem external_realized : ∃ x,
    (cubic.withCoefficients explicitGeneration correspondence).NonzeroInput x := by
  obtain ⟨x,hx⟩ := cubic_realized
  exact ⟨x, (cubic.nonzero_withCoefficients_iff explicitGeneration correspondence x).mpr hx⟩

def differenceModel : DipoleCouplingModel.Couplings (X := Fin 2 → ℂ) (Y := ℂ)
    flavor flavor flavor where
  incoming := (((Pi.basisFun ℂ (Fin 2)).coord 0) -
    ((Pi.basisFun ℂ (Fin 2)).coord 1)).smulRight (IntertwiningMap.id flavor)
  outgoingB := (_root_.LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight bridge
  outgoingW := 0
  propagator := IntertwiningMap.id flavor

def equalCoordinates (_ : Fin 2) : MvPolynomial Unit ℂ := X ()
def cancelling := DipolePolynomialAutomation.register flavor flavor flavor differenceModel
  (Pi.basisFun ℂ (Fin 2)) scalarBasis equalCoordinates outgoingCoordinates
  (fun _ => Set.univ) mu electron
def cancellingCertificate := DipolePolynomialAutomation.certificate flavor flavor flavor differenceModel
  (Pi.basisFun ℂ (Fin 2)) scalarBasis equalCoordinates outgoingCoordinates
  (fun _ => Set.univ) mu electron (fun _ => Set.infinite_univ)

theorem cancelling_selected (x : Unit → ℂ) : cancelling.observe x = 0 := by
  rw [cancelling, DipolePolynomialAutomation.selected]
  simp [differenceModel, PolynomialBasisCoordinates.evaluate, equalCoordinates,
    outgoingCoordinates, scalarBasis, Fin.sum_univ_two, Module.Basis.coord_apply]

theorem cancelling_grouped_zero : ∀ d, cancellingCertificate.grouped d = 0 := by
  apply cancellingCertificate.no_nonzero_iff.mp
  intro x hx
  exact hx.2 (cancelling_selected x)

def finiteDomain := DipolePolynomialAutomation.register flavor flavor flavor
  (DipoleCouplingControls.model 1) scalarBasis scalarBasis incomingCoordinates outgoingCoordinates
  (fun _ => {0}) mu electron

theorem finite_domain_no_nonzero : ∀ x, ¬ finiteDomain.NonzeroInput x := by
  intro x hx
  have hz : x () = 0 := hx.1 () (Set.mem_univ ())
  have he : finiteDomain.observe x = cubic.observe x := rfl
  apply hx.2
  rw [he, cubic_selected, hz]
  simp

end
end GUT.DipolePolynomialAutomationExamples
