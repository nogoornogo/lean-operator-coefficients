import GUT.SU6.Branching.ConcreteSU6PhysicalTarget

open Math

/-!
# Audit of the concrete source's physical Standard Model character

These declarations connect actual analytic SU(6) traces to the existing
physical-torus target and its faithful charge-resolved normal form. No
mass map, full zero-mode spectrum, or Dirac model inhabitant is asserted.
-/

#print axioms GUT.ConcreteSU6PhysicalTarget.physicalDiagonalPoint_last
#print axioms GUT.ConcreteSU6PhysicalTarget.physicalDiagonalPoint_coords
#print axioms GUT.ConcreteSU6PhysicalTarget.smExponent_eq
#print axioms GUT.ConcreteSU6PhysicalTarget.mFourier_neg_eq_inv
#print axioms GUT.ConcreteSU6PhysicalTarget.eval_integralSMCharacter
#print axioms GUT.ConcreteSU6PhysicalTarget.ten_add_antifive_eq_SM
#print axioms GUT.ConcreteSU6PhysicalTarget.signed_character_physical
#print axioms GUT.ConcreteSU6PhysicalTarget.signedSource_character
#print axioms GUT.ConcreteSU6PhysicalTarget.signedSource_integralCharacter
#print axioms GUT.ConcreteSU6PhysicalTarget.uniform_sourcePhysicalResolvedCharacter
#print axioms GUT.ConcreteSU6PhysicalTarget.signedSource_resolvedCharacter
#print axioms GUT.ConcreteSU6PhysicalTarget.signedSource_coefficientSpectrum
#print axioms GUT.ConcreteSU6PhysicalTarget.signedSource_isSMTargetCharacterEquivalent

namespace GUT.AuditConcreteSU6PhysicalTarget

open ConcreteSU6PhysicalTarget PhysicalChargeResolvedBridge

/-- A nonzero torsion charge is allowed in the coefficient-level theorem. -/
example :
    sourcePhysicalResolvedCharacter (-2) 3 (signedSource (1 : ZMod 2)) =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges (1 : ZMod 2)) 0 :=
  signedSource_resolvedCharacter _

/-- Neutral residual characters work for every Abelian group, finite ones included. -/
example (H : Type*) [CommGroup H] :
    IsExactSMOnlyPhysicalCoefficientSpectrum
      (sourcePhysicalResolvedCharacter (-2) 3
        (signedSource (0 : FiniteAbelianChargeSectors.ChargeLabel H)))
      1 (uniformCharges 0) 0 :=
  signedSource_coefficientSpectrum _

end GUT.AuditConcreteSU6PhysicalTarget
