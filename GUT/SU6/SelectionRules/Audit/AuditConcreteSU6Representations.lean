import GUT.SU6.Representations.ConcreteSU6Representations

open Math

/-!
# Audit of concrete continuous SU(6) matter representations

These checks cover the analytic `6`, `bar6`, and `15`, their exact algebraic
equivalences, and the transported torus certificates. They do not assert a
mass map or an exact Standard Model light spectrum for a concrete model.
-/

#print axioms Math.FiniteBasisHilbertization.Copy.continuous_iff_coords
#print axioms Math.ContinuousUnitaryConstructions.jointlyContinuous_of_orbit
#print axioms Math.ContinuousUnitaryConstructions.basisCopyRepresentation_jointlyContinuous
#print axioms Math.ContinuousUnitaryConstructions.jointlyContinuous_tprod
#print axioms Math.ContinuousUnitaryConstructions.unitary_tprod
#print axioms GUT.ContinuousUnitaryConstructions.ContinuousUnitarySU6Representation.dualSeedRho_jointlyContinuous
#print axioms GUT.ContinuousUnitaryConstructions.ContinuousUnitarySU6Representation.dualEquiv
#print axioms GUT.CertifiedConstructions.exteriorLinearEquiv
#print axioms GUT.CertifiedConstructions.exteriorEquiv
#print axioms GUT.CertifiedConstructions.dualEquiv
#print axioms GUT.ConcreteSU6Representations.fundamentalRho_unitary
#print axioms GUT.ConcreteSU6Representations.fundamentalRho_jointlyContinuous
#print axioms GUT.ConcreteSU6Representations.fundamentalWitness
#print axioms GUT.ConcreteSU6Representations.antifundamental_finrank
#print axioms GUT.ConcreteSU6Representations.antifundamentalWitness
#print axioms GUT.ConcreteSU6Representations.exteriorTwo_basisOrbit_continuous
#print axioms GUT.ConcreteSU6Representations.exteriorTwoSeedRho_jointlyContinuous
#print axioms GUT.ConcreteSU6Representations.exteriorTwo_finrank
#print axioms GUT.ConcreteSU6Representations.exteriorTwoWitness
#print axioms GUT.ConcreteSU6Representations.exteriorTwoTorusEigenbasis
#print axioms GUT.ConcreteSU6Representations.antifundamentalTorusEigenbasis
#print axioms GUT.ConcreteSU6Representations.alternatingSquareSubrepresentation
#print axioms GUT.ConcreteSU6Representations.alternatingSquare
