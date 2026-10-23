import GUT.SU6.SelectionRules.Models.ContinuousWeylModel
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylBenchmark

open Physics

open Math

/-!
# Non-vacuity of the continuous-geometry symmetric mass model

The old fixed-standard model supplies an independently proved ultraviolet
dual target. This constructs a new canonical model with continuous geometry
and zero mass. It does not claim to preserve the old mass or its radical.
-/

set_option autoImplicit false

namespace GUT.ContinuousWeylBenchmark

noncomputable section

open StandardWeylMassSource PhysicalWeylMassSource InvariantWeylMass
open PhysicalChargeResolvedBridge PhysicalWeylMomentBridge ContinuousWeylModel
open StandardPhysicalSource (FiniteChargedContinuousUnitarySource)
open StandardSMCharacterTarget (ChargeLabel)

variable {H : Type*} [CommGroup H]

theorem standardSource_dualTarget (M : StandardWeylModel H) :
    chiralDifference (ordinaryPhysicalResolvedCharacter (-2) 3 M.matter) =
      chiralDifference (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets) := by
  have hz : FiniteAbelianChargeSectors.centralDegreeCharge (1 : H →* Circle) = 0 := by
    ext z
    apply Additive.toMul.injective
    simp [FiniteAbelianChargeSectors.centralDegreeCharge]
  have ht := StandardWeylDualTarget.chiralDifference_eq_target_of_mass M.mass
    (ordinaryFields M.matter).unitary
    ((ordinaryChargedSource M.matter).resolvedCharacter
      (FiniteAbelianChargeSectors.centralDegreeCharge (1 : H →* Circle)))
    (fun x h => (ordinaryFields_character M.matter M.nonnegative (Multiplicative.ofAdd x, h)).trans
      (StandardPhysicalCharacterBridge.sourceProductRepresentation_character 1
        (ordinaryChargedSource M.matter) x h))
    M.generations M.charges M.singlets M.lightTarget
  rw [hz] at ht
  have he := congrArg embedStandardCharacter ht
  simpa only [ordinaryPhysicalResolvedCharacter, sourcePhysicalResolvedCharacter_standard,
    exactSMWithSingletsResolvedCharacter_standard,
    PhysicalWeylChargeBridge.embedStandardCharacter_chiralDifference] using he

def ofStandardWithZeroMass (M : StandardWeylModel H) : ContinuousWeylMassModel H where
  geometry := ConcreteStandardGeometry.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  mass := SymmetricMass.zero _
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := by
    apply lightTarget_of_dualResolved _ _ _ M.nonnegative
    rw [ConcreteStandardGeometry.hyperchargePair_eq_standard]
    exact standardSource_dualTarget M

def model (H : Type*) [CommGroup H] : ContinuousWeylMassModel H :=
  ofStandardWithZeroMass (ConcreteWeylBenchmark.model H)

theorem model_mass_zero : (model H).mass.form = 0 := rfl

theorem exists_one_generation_model (H : Type*) [CommGroup H] :
    ∃ M : ContinuousWeylMassModel H, M.generations = 1 := ⟨model H, rfl⟩

end

end GUT.ContinuousWeylBenchmark
