import GUT.SU6.SelectionRules.Models.DiracPhysicalModel

open Physics

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

#print axioms Physics.DiracYukawaMass.InvariantBareMass.toIntertwiningMap
#print axioms Physics.DiracYukawaMass.InvariantBareMass.ofIntertwiningMap_toIntertwiningMap
#print axioms Physics.DiracYukawaMass.EquivariantYukawa.zero
#print axioms Physics.DiracYukawaMass.InvariantVacuum.zero
#print axioms Physics.DiracYukawaMass.Sector.zero_inducedMass
#print axioms Physics.DiracYukawaMass.Sector.inducedMass_equivariant
#print axioms Physics.DiracYukawaMass.Sector.massMap
#print axioms Physics.DiracYukawaMass.Sector.toInvariantMassPairing
#print axioms Physics.DiracYukawaMass.Sector.toInvariantMassPairing_toIntertwiningMap
#print axioms Physics.DiracYukawaMass.Sector.ofBareMass_massMap
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
