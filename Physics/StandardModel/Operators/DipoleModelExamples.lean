import Physics.StandardModel.Operators.DipoleMatrixInterface
import Physics.StandardModel.Operators.DipoleCouplingControls

open Math

/-! Compiled model-author examples. Algebraic samples, not physical matching. -/
namespace GUT.DipoleModelExamples
set_option autoImplicit false
noncomputable section
open Representation DipoleModelInterface DipoleControls MvPolynomial

def residualModel : Registered (X := ℂ) flavor flavor :=
  ofResidual flavor flavor Set.univ mu electron (fun z => (z^2 • bridge,0))

def externalModel : Registered (X := ℂ) flavor flavor :=
  residualModel.withCoefficients DipoleControls.generation
    (by intro z _; simp [residualModel, ofResidual, DipoleControls.generation])

theorem external_nonzero_iff (z : ℂ) : externalModel.NonzeroInput z ↔ z ≠ 0 := by
  change (z ∈ Set.univ ∧ DipoleFlavorSelection.selector flavor flavor mu electron
    (DipoleControls.generation z) ≠ 0) ↔ _
  simp

def correlated : Registered (X := ℂ) flavor flavor :=
  ofCouplings flavor flavor flavor (DipoleCouplingControls.model 1) Set.univ
    (fun z => z^2) (fun z => z) mu electron

theorem correlated_selected (z : ℂ) : correlated.observe z = (z^3,0) :=
  DipoleCouplingControls.nonlinear_pullback z

theorem correlated_nonzero_iff (z : ℂ) : correlated.NonzeroInput z ↔ z ≠ 0 := by
  change (z ∈ Set.univ ∧ correlated.observe z ≠ 0) ↔ _
  rw [correlated_selected]
  simp

def cubicPaths (_ : Fin 1) : IntertwiningMap flavor flavor × IntertwiningMap flavor flavor :=
  (bridge,0)
def cubicWeights (_ : Fin 1) : MvPolynomial Unit ℂ := (X ())^3
def cubic : Registered (X := Unit → ℂ) flavor flavor :=
  ofResidual flavor flavor (Set.pi Set.univ (fun _ => Set.univ)) mu electron
    (WeightedSelectedPaths.synthesis cubicPaths
      (fun x i => eval x (cubicWeights i)))

def cubicCertificate : PolynomialCertificate (I := Fin 1) flavor flavor cubic where
  coordinates _ := Set.univ
  infinite _ := Set.infinite_univ
  domain_eq := rfl
  paths := cubicPaths
  weights := cubicWeights
  expansion _ _ := rfl

theorem cubic_realized : ∃ x, cubic.NonzeroInput x := by
  apply cubicCertificate.exists_nonzero_iff.mpr
  refine ⟨Finsupp.single () 3, ?_⟩
  simp [PolynomialCertificate.grouped, cubicCertificate, cubicPaths, cubicWeights,
    cubic, ofResidual, MvPolynomial.X_pow_eq_monomial]

def cancellingPaths (i : Fin 2) : IntertwiningMap flavor flavor × IntertwiningMap flavor flavor :=
  if i = 0 then (bridge,0) else (-bridge,0)
def cancelling : Registered (X := Unit → ℂ) flavor flavor :=
  ofResidual flavor flavor (Set.pi Set.univ (fun _ => Set.univ)) mu electron
    (WeightedSelectedPaths.synthesis cancellingPaths
      (fun x (_ : Fin 2) => eval x ((X ())^3)))

def cancellingCertificate : PolynomialCertificate (I := Fin 2) flavor flavor cancelling where
  coordinates _ := Set.univ
  infinite _ := Set.infinite_univ
  domain_eq := rfl
  paths := cancellingPaths
  weights _ := (X ())^3
  expansion _ _ := rfl

theorem cancelling_no_nonzero : ∀ x, ¬ cancelling.NonzeroInput x := by
  apply cancellingCertificate.no_nonzero_iff.mpr
  intro d
  simp [PolynomialCertificate.grouped, cancellingCertificate, cancellingPaths,
    cancelling, ofResidual, Fin.sum_univ_two]

def matrices (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ![![0,z^3],![0,0]]
def matrixModel : Registered (X := ℂ) flavor flavor :=
  DipoleMatrixInterface.register flavor flavor Set.univ 1 0 matrices (fun _ => 0)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem matrix_selected (z : ℂ) : matrixModel.observe z = (z^3,0) := by
  simpa [matrixModel, matrices] using DipoleMatrixInterface.selected_entry
    flavor flavor Set.univ 1 0 matrices (fun _ => 0)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) z (Set.mem_univ z)

theorem matrix_nonzero_iff (z : ℂ) : matrixModel.NonzeroInput z ↔ z ≠ 0 := by
  change (z ∈ Set.univ ∧ matrixModel.observe z ≠ 0) ↔ _
  rw [matrix_selected]
  simp

theorem restricted_zero_unreachable :
    ¬ ∃ z, ((matrixModel.restrict {z | z ≠ 0}).pullback (fun _ : Unit => 0)).NonzeroInput z := by
  simp only [Registered.nonzero_pullback_iff, Registered.nonzero_restrict_iff]
  simp

end
end GUT.DipoleModelExamples
