import Math.LieGroups.Torus.CircleHomTangent

open Math

/-!
# Axiom audit for the circle cocharacter lattice

This file keeps the covering-space proof of the integer classification easy
to re-audit after dependency or Lean upgrades.
-/

#print axioms Math.CircleHomLattice.existsUnique_eq_circlePowerHom
#print axioms Math.CircleHomLattice.circlePowerHom_injective
#print axioms Math.CircleHomLattice.existsUnique_eq_circlePairPowerHom
#print axioms Math.CircleHomLattice.integerPairEquivCircleTorusHom
#print axioms Math.CircleHomLattice.forall_pow_eq_one_imp_eq_one_iff
#print axioms Math.CircleHomLattice.circlePairPowerHom_injective_iff
#print axioms Math.CircleHomLattice.hasDerivAt_circlePowerCoefficientCurve
