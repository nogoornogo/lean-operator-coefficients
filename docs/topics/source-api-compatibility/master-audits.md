# Master-State Focused Checks

Each source below was directly elaborated on master with `lake env lean -j2`,
one compiler at a time, with the unchanged 16 GiB address-space cap and
540-second timeout. Core dumps were disabled. Dependencies were reused;
these commands rerun the source consumers and audit code rather than
accepting replayed Lake messages. The first four sources are legacy-client
controls; the remaining sources are the original proof audits and the
new structural/model inventories.

| Direct source | Result |
| --- | --- |
| [Physics/Compatibility/Audit/AbelianMassSpectrum.lean](../../../Physics/Compatibility/Audit/AbelianMassSpectrum.lean) | PASS |
| [Physics/Compatibility/Audit/Structures.lean](../../../Physics/Compatibility/Audit/Structures.lean) | PASS |
| [Physics/Compatibility/Audit/LegacyInputs.lean](../../../Physics/Compatibility/Audit/LegacyInputs.lean) | PASS |
| [GUT/Compatibility/Audit/LegacyRestriction.lean](../../../GUT/Compatibility/Audit/LegacyRestriction.lean) | PASS |
| [Math/RepresentationTheory/Tensors/Audit/AuditSixSlotRestrictionLift.lean](../../../Math/RepresentationTheory/Tensors/Audit/AuditSixSlotRestrictionLift.lean) | PASS |
| [Math/RepresentationTheory/Content/Audit/AuditSixSlotSpeciesSum.lean](../../../Math/RepresentationTheory/Content/Audit/AuditSixSlotSpeciesSum.lean) | PASS |
| [Physics/StandardModel/Gauge/Tensors/Audit/AuditSixColorInvariant.lean](../../../Physics/StandardModel/Gauge/Tensors/Audit/AuditSixColorInvariant.lean) | PASS |
| [Math/LieGroups/E6/Audit/AuditMinusculeCompact.lean](../../../Math/LieGroups/E6/Audit/AuditMinusculeCompact.lean) | PASS |
| [Math/LieGroups/E6/Audit/AuditMatrixLieAlgebra.lean](../../../Math/LieGroups/E6/Audit/AuditMatrixLieAlgebra.lean) | PASS |
| [Math/LieGroups/E6/Audit/AuditGeckComparison.lean](../../../Math/LieGroups/E6/Audit/AuditGeckComparison.lean) | PASS |
| [Physics/StandardModel/Operators/BaryonTwo/Li/Audit/AuditLiSixQuarkSourceDerivation.lean](../../../Physics/StandardModel/Operators/BaryonTwo/Li/Audit/AuditLiSixQuarkSourceDerivation.lean) | PASS |
| [Physics/StandardModel/Operators/Selection/Audit/AuditFlavoredCyclicSelection.lean](../../../Physics/StandardModel/Operators/Selection/Audit/AuditFlavoredCyclicSelection.lean) | PASS |
| [GUT/E6/Audit/AuditSU5Inclusion.lean](../../../GUT/E6/Audit/AuditSU5Inclusion.lean) | PASS |
| [GUT/SU5/Audit/AuditInvariantMassNormalForm.lean](../../../GUT/SU5/Audit/AuditInvariantMassNormalForm.lean) | PASS |
| [GUT/SU5/Audit/AuditActualFullFamily.lean](../../../GUT/SU5/Audit/AuditActualFullFamily.lean) | PASS |
| [Physics/StandardModel/Operators/BaryonTwo/Coefficients/Audit/AuditDeltaBTwoContractionRelations.lean](../../../Physics/StandardModel/Operators/BaryonTwo/Coefficients/Audit/AuditDeltaBTwoContractionRelations.lean) | PASS |
| [Math/Algebra/HiggsFourWaveCubature/Structural/Audit.lean](../../../Math/Algebra/HiggsFourWaveCubature/Structural/Audit.lean) | PASS |
| [Math/Algebra/HiggsFourWaveCubature/Structural/RemainingAudit.lean](../../../Math/Algebra/HiggsFourWaveCubature/Structural/RemainingAudit.lean) | PASS |
| [Math/Algebra/Constructions/Audit/AuditHiggsQuarticFourFoundations.lean](../../../Math/Algebra/Constructions/Audit/AuditHiggsQuarticFourFoundations.lean) | PASS |
| [Physics/FieldTheory/Jets/Higgs/QuarticFour/Audit/AuditHiggsQuarticFour.lean](../../../Physics/FieldTheory/Jets/Higgs/QuarticFour/Audit/AuditHiggsQuarticFour.lean) | PASS |
| [Physics/FieldTheory/Jets/Higgs/QuarticFour/Audit/AuditHiggsQuarticFourCompleteness.lean](../../../Physics/FieldTheory/Jets/Higgs/QuarticFour/Audit/AuditHiggsQuarticFourCompleteness.lean) | PASS |
| [Math/RepresentationTheory/Fields/Audit/AuditFieldConnections.lean](../../../Math/RepresentationTheory/Fields/Audit/AuditFieldConnections.lean) | PASS |
| [Physics/FieldTheory/Fields/Audit/AuditFieldConnections.lean](../../../Physics/FieldTheory/Fields/Audit/AuditFieldConnections.lean) | PASS |
| [GUT/SU6/Audit/AuditFieldConnection.lean](../../../GUT/SU6/Audit/AuditFieldConnection.lean) | PASS |
| [Math/RepresentationTheory/Constructions/Audit/AuditEulerNaturality.lean](../../../Math/RepresentationTheory/Constructions/Audit/AuditEulerNaturality.lean) | PASS |
| [Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditEulerNaturality.lean](../../../Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditEulerNaturality.lean) | PASS |
| [GUT/SU6/Audit/AuditBoundaryProtection.lean](../../../GUT/SU6/Audit/AuditBoundaryProtection.lean) | PASS |
| [Physics/FieldTheory/Jets/Lagrangian/Audit/AuditLagrangianModel.lean](../../../Physics/FieldTheory/Jets/Lagrangian/Audit/AuditLagrangianModel.lean) | PASS |
| [GUT/SU6/Audit/AuditProtectionFeasibility.lean](../../../GUT/SU6/Audit/AuditProtectionFeasibility.lean) | PASS |
| [GUT/SU6/Audit/AuditPhysicalIndexObstruction.lean](../../../GUT/SU6/Audit/AuditPhysicalIndexObstruction.lean) | PASS |

The structural checks include 109 pilot-owned and 280 all-family declarations.
The original Math-only Higgs foundation inventory checks 788 declarations;
its original physical completeness consumer also passes. The seven shared-
connection and Euler/Lagrangian/boundary regressions retain their recorded
1,128 transitive checks. These inventories overlap; they are not a count
of distinct project theorems.

The [integration record](master-integration.md) gives the merge chain, full
build, exact source/API/inventory comparisons and remaining boundaries.
