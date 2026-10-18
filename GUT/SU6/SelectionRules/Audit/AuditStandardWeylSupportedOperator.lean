import GUT.SU6.SelectionRules.StandardBranch.StandardWeylSupportedOperator

/-!
# Audit of the supported-operator witness

Checks that the new declarations use only standard axioms and that the
conditional UV `SupportedInvariantOperator` construction specializes to a
finite Abelian group. These examples assume `hOrbit`; they do not construct
zero-mode support or establish non-vacuity of that extra hypothesis.
-/

set_option autoImplicit false

namespace GUT.AuditStandardWeylSupportedOperator

open StandardWeylSupportedOperator
open StandardWeylMassSource
open StandardBranchProtonObstruction
open FiniteAbelianChargeSectors
open StandardSMCharacterTarget (ChargeLabel)
open StandardModelLocalOperator (SupportedInvariantOperator StandardOperatorClass
    ForbidsEverySupportedStandardOperator ForbidsEverySupportedPhysicalDeltaBOneOperator)

example (M : StandardWeylModel (Multiplicative (ZMod 2)))
    (hOrbit : nonzeroOrbitProfiles M) :
    Nonempty (SupportedInvariantOperator (pUV M)) :=
  ⟨supportedQqueWitness M hOrbit⟩

example (M : StandardWeylModel (Multiplicative (ZMod 2)))
    (hOrbit : nonzeroOrbitProfiles M) :
    (supportedQqueWitness M hOrbit).operator = StandardOperatorClass.qque := by
  unfold supportedQqueWitness StandardModelLocalOperator.supportedQque
  rfl

example (M : StandardWeylModel (Multiplicative (ZMod 2)))
    (hOrbit : nonzeroOrbitProfiles M) :
    (supportedDuqlWitness M hOrbit).operator = StandardOperatorClass.duql := by
  unfold supportedDuqlWitness StandardModelLocalOperator.supportedDuql
  rfl

example (M : StandardWeylModel (Multiplicative (ZMod 2))) :
    SU5OrbitCompatible M.charges :=
  su5OrbitCompatible M

example (M : StandardWeylModel (Multiplicative (ZMod 2))) :
    protonFirstCharacter M.charges = 1 ∧ protonSecondCharacter M.charges = 1 :=
  protonCharacters_eq_one M

example [Finite (Multiplicative (ZMod 2))]
    (M : StandardWeylModel (Multiplicative (ZMod 2)))
    (hOrbit : nonzeroOrbitProfiles M) :
    ¬ ForbidsEverySupportedStandardOperator (pUV M) :=
  finiteAbelian_not_forbidsEverySupportedStandardOperator M hOrbit

#print axioms su5OrbitCompatible
#print axioms pUV_isWeylInvariant
#print axioms chargesSupported
#print axioms supportedQqueWitness
#print axioms supportedDuqlWitness
#print axioms not_forbidsEverySupportedStandardOperator
#print axioms not_forbidsEverySupportedPhysicalDeltaBOneOperator

end GUT.AuditStandardWeylSupportedOperator
