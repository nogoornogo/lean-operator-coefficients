import Physics.StandardModel.Operators.SMCompactTorus
import Physics.StandardModel.Operators.SMWeylExtractionInput

/-! Actual mixed-content local multiplicities with only the explicit Weyl
reduction theorem left as external mathematical input. -/
namespace GUT.SMCompactMultiplicity
set_option autoImplicit false
noncomputable section
open Math Representation SMCompactTorus

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group :=
  borel SMCombinedCompactAction.Group
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)

abbrev model := SMCombinedCompactContinuity.model flavor p m delta

def polynomial : Weight →₀ ℤ := FiniteTorusPresentation.inverseCoefficients
  (model flavor p m delta) (SMCombinedCompactContinuity.continuous_model flavor p m delta) inclusion

theorem presents : CompactWeylExtraction.Presents (model flavor p m delta) inclusion.toMonoidHom
    monomial (polynomial flavor p m delta) := by
  intro t
  exact (FiniteTorusPresentation.inverse_presentation (model flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) inclusion t).symm

/-- A specialization of established Weyl reduction, not a custom axiom.
The compact model, comparison, continuity and presentation are constructed. -/
abbrev Input := CompactWeylExtraction.TorusReduction (model flavor p m delta) inclusion.toMonoidHom monomial roots

def multiplicity : ℤ := CompactWeylExtraction.constantTerm roots (polynomial flavor p m delta)

variable (input : Input flavor p m delta)
include input in
theorem kernel_dimension_int : (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) : ℤ) =
    multiplicity flavor p m delta :=
  SMWeylExtractionInput.kernel_dimension_int flavor p m delta (model flavor p m delta) inclusion.toMonoidHom
    monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial flavor p m delta) (presents flavor p m delta)

include input in
theorem nonnegative : 0 ≤ multiplicity flavor p m delta :=
  SMWeylExtractionInput.multiplicity_nonnegative flavor p m delta (model flavor p m delta) inclusion.toMonoidHom
    monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial flavor p m delta) (presents flavor p m delta)

include input in
theorem kernel_dimension : Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) =
    (multiplicity flavor p m delta).toNat :=
  SMWeylExtractionInput.kernel_dimension flavor p m delta (model flavor p m delta) inclusion.toMonoidHom
    monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial flavor p m delta) (presents flavor p m delta)

include input in
theorem rank_formula : Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
    SMIteratedContent.columns p m - (multiplicity flavor p m delta).toNat :=
  SMWeylExtractionInput.rank_formula flavor p m delta (model flavor p m delta) inclusion.toMonoidHom
    monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial flavor p m delta) (presents flavor p m delta)

include input in
theorem local_allowed_iff : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor p m delta)) ↔ 0 < multiplicity flavor p m delta :=
  SMWeylExtractionInput.local_allowed_iff flavor p m delta (model flavor p m delta) inclusion.toMonoidHom
    monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial flavor p m delta) (presents flavor p m delta)

end
end GUT.SMCompactMultiplicity
