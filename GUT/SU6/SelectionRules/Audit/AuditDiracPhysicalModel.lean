import GUT.SU6.SelectionRules.Models.DiracPhysicalModel

/-!
# Axiom audit for the finite-dimensional Dirac model bridge

This audit covers the physical-source milestone in which an invariant bare
mass, an equivariant Yukawa family, and an invariant vacuum construct the
post-vacuum Dirac mass map.  The scoped model retains the exact Standard Model
chiral index as an explicit applicability condition and feeds the resulting
mass pairing into the continuity-only E assembly.

No declaration audited here interprets the mass data as a general Weyl or
Majorana bilinear, derives the Standard Model chiral index from an arbitrary
Lagrangian, or proves a nonzero decay amplitude.
-/

#print axioms GUT.DiracYukawaMass.InvariantBareMass.toIntertwiningMap
#print axioms GUT.DiracYukawaMass.InvariantBareMass.ofIntertwiningMap_toIntertwiningMap
#print axioms GUT.DiracYukawaMass.EquivariantYukawa.zero
#print axioms GUT.DiracYukawaMass.InvariantVacuum.zero
#print axioms GUT.DiracYukawaMass.Sector.zero_inducedMass
#print axioms GUT.DiracYukawaMass.Sector.inducedMass_equivariant
#print axioms GUT.DiracYukawaMass.Sector.massMap
#print axioms GUT.DiracYukawaMass.Sector.toInvariantMassPairing
#print axioms GUT.DiracYukawaMass.Sector.toInvariantMassPairing_toIntertwiningMap
#print axioms GUT.DiracYukawaMass.Sector.ofBareMass_massMap
#print axioms GUT.DiracPhysicalModel.HasExactSMChiralIndex
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.massMap
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.massPairing
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.toInvariantMassPairingSource
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.hyperchargePair_eq_standard
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.coefficientSpectrum
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.supportedInvariantOperator
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.not_forbidsEverySupportedProtonOperator
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.ofInvariantMassPairingSource
#print axioms GUT.DiracPhysicalModel.ContinuousDiracYukawaModel.ofInvariantMassPairingSource_massMap
