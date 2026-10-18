import GUT.SU6.Representations.UnitaryVirtualRestriction
import GUT.SU6.SelectionRules.Models.PhysicalChargedCharacterBridge
import Math.RepresentationTheory.Unitary.CommutingUnitaryActions

open Math

/-! Actual SU(6) times residual-group actions underlying the old physical
torus fields. Restriction recovers the complete bundled fields, not just trace. -/

set_option autoImplicit false

namespace GUT.ChargedAmbientRealization

noncomputable section

open UnitaryVirtualRealization StandardPhysicalSource
open PhysicalChargedCharacterBridge

variable {H : Type*} [CommGroup H]

abbrev AmbientGroup (H : Type*) [CommGroup H] := ActualRestriction.SU6 × H

def physicalInclusion (m n : ℤ) :
    PhysicalChargeResolvedEvaluation.CombinedGroup H →* AmbientGroup H :=
  (PhysicalSMTorusTarget.embedding m n).prodMap (MonoidHom.id H)

def summand (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation (AmbientGroup H) where
  V := s.rep.V
  rho := CommutingUnitaryActions.charged s.rep.rho s.offset.toMul
  unitary := CommutingUnitaryActions.charged_unitary _ _ s.rep.unitary

theorem restrict_summand (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    (summand s).restrict (physicalInclusion m n) = chargedPhysicalUnitaryRepresentation m n s := by
  have he : (summand s).rho.comp (physicalInclusion m n) = chargedPhysicalRho m n s := by
    ext g v
    rfl
  change ActualUnitaryGroupRepresentation.mk s.rep.V _ _ = _
  cases he
  rfl

def source : FiniteChargedContinuousUnitarySource (ChargeLabel H) →
    FiniteUnitaryVirtualRepresentation (AmbientGroup H)
  | [] => []
  | s :: ss => ⟨s.coeff, summand s⟩ :: source ss

theorem restrict_source (m n : ℤ) (ss : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    FiniteUnitaryVirtualRepresentation.restrict (physicalInclusion m n) (source ss) =
      sourceUnitaryRepresentation m n ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [source, FiniteUnitaryVirtualRepresentation.restrict,
      sourceUnitaryRepresentation, restrict_summand, ih]

def positive (ss : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation (AmbientGroup H) :=
  FiniteUnitaryVirtualRepresentation.positive (source ss)

theorem restrict_positive (m n : ℤ) (ss : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    (positive ss).restrict (physicalInclusion m n) =
      FiniteUnitaryVirtualRepresentation.positive (sourceUnitaryRepresentation m n ss) := by
  rw [positive, FiniteUnitaryVirtualRepresentation.restrict_positive, restrict_source]

end

end GUT.ChargedAmbientRealization
