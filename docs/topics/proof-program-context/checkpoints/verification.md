# verification

Environment-specific paths were normalized at stage 01; recorded outcomes are unchanged. Commands assume elan, lake and lean on PATH and execution from the repository root.

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

## Verification

```bash
lake build Math.RepresentationTheory.Characters.Audit.AuditCharacterRestriction
lake build Math.RepresentationTheory.Characters.Audit.AuditCharacterExact
lake build Math.RepresentationTheory.Multiplicity.Audit.AuditMultiplicityCommutant
lake build
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteSU6Representations.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditDiracPhysicalModel.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditDiracWeylConvention.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteSU6Branching.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteSU6PhysicalTarget.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditActualBlockChoiceIndependence.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteDiracBenchmark.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditInvariantWeylMass.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardWeylDualTarget.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardWeylMassSource.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteWeylBenchmark.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardWeylSupportedOperator.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditWeylZeroModeSupport.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditWeylConjugateOperator.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditConcreteWeylFullMass.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditPhysicalWeylChargeBridge.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditContinuousWeylModel.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditContinuousWeylFullMass.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditWeylYukawa.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMGaugeTensor.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMRadicalTensor.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMBranching.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMUVMass.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMOrdinaryModel.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMUVYukawa.lean
lake env lean GUT/SU6/ProtonStabilityNoGo/Audit/AuditStandardSMUVStabilizer.lean
```
