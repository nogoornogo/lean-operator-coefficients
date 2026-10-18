import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Physics.StandardModel.Operators.DeltaBTwoLocalOperator
import Math.RepresentationTheory.SixSlotSpeciesTransport
import Math.RepresentationTheory.SixSlotRestrictionLift

open Math

/-! Explicit residual multiplicities and actual-field inputs for the all-right
six-quark sector. This interface does not assert residual Hom completeness. -/
namespace GUT.DeltaBTwoModelInterface
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

variable {H U D : Type*} [Group H]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  (u : Representation ℂ H U) (d : Representation ℂ H D)

abbrev SymmetryGroup (H : Type*) :=
  (StandardSMGaugeTensor.GaugeGroup × H) × WeylSpinor.Group

def upModel : Representation ℂ (SymmetryGroup H)
    ((SMEpsilonTensor.Color ⊗[ℂ] U) ⊗[ℂ] WeylSpinor.Space) :=
  external (external StandardSMGaugeTensor.upRight u) WeylSpinor.right
def downModel : Representation ℂ (SymmetryGroup H)
    ((SMEpsilonTensor.Color ⊗[ℂ] D) ⊗[ℂ] WeylSpinor.Space) :=
  external (external StandardSMGaugeTensor.downRight d) WeylSpinor.right

/-- Independent invariant Hom sector, not the image of a contraction assembly. -/
abbrev ModelSector := ↥(SixSlotSpeciesDegree.sector
  (H := SymmetryGroup H)
  (A := (SMEpsilonTensor.Color ⊗[ℂ] U) ⊗[ℂ] WeylSpinor.Space)
  (B := (SMEpsilonTensor.Color ⊗[ℂ] D) ⊗[ℂ] WeylSpinor.Space)
  (upModel u) (downModel d))

abbrev OrderedCoefficient := IntertwiningMap
  (SixSlotAlternation.orderedRepresentation
    (H := SymmetryGroup H)
    (A := (SMEpsilonTensor.Color ⊗[ℂ] U) ⊗[ℂ] WeylSpinor.Space)
    (B := (SMEpsilonTensor.Color ⊗[ℂ] D) ⊗[ℂ] WeylSpinor.Space)
    (upModel u) (downModel d))
  (Representation.trivial ℂ (SymmetryGroup H) ℂ)

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ (SymmetryGroup H) A)
  (b : Representation ℂ (SymmetryGroup H) B)

/-- Exhaustiveness of alternating descent on actual fields, before factorization. -/
theorem exists_ordered (f : SixSlotSpeciesDegree.sector a b) :
    ∃ g : IntertwiningMap (SixSlotAlternation.orderedRepresentation a b)
      (Representation.trivial ℂ (SymmetryGroup H) ℂ),
      SixSlotAlternation.coefficient a b g = f.val :=
  SixSlotRestrictionLift.exists_ordered a b f.val f.property

/-- Supplied model correspondence; no coefficient or nonzero premise is included. -/
structure Inputs where
  upEquiv : Representation.Equiv a (upModel u)
  downEquiv : Representation.Equiv b (downModel d)

def onFieldsEquiv (i : Inputs u d a b) :
    ModelSector u d ≃ₗ[ℂ] SixSlotSpeciesDegree.sector a b :=
  SixSlotSpeciesTransport.equiv i.upEquiv i.downEquiv

theorem exists_on_fields_iff (i : Inputs u d a b) :
    (∃ f : SixSlotSpeciesDegree.sector a b, f ≠ 0) ↔
      ∃ f : ModelSector u d, f ≠ 0 :=
  (SixSlotSpeciesTransport.exists_nonzero_iff i.upEquiv i.downEquiv).symm

/-- The fixed species pattern has baryon number two independently of multiplicities.
This is a grading statement, not invariance under baryon-number symmetry. -/
theorem species_baryon_grade :
    DeltaBTwoLocalOperator.baryonGrade DeltaBTwoLocalOperator.udduddOperator = 6 :=
  DeltaBTwoLocalOperator.uddudd_baryonGrade

end
end GUT.DeltaBTwoModelInterface
