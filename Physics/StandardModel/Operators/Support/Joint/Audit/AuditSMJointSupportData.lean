import Math.RepresentationTheory.Constructions.Audit.AuditJointSourceReexpression
import Physics.StandardModel.Operators.Support.Joint.SMJointSupportDataExamples
run_cmd do
  let ds := [
    ``Physics.SMCoreSourceData.coreData,
    ``Physics.SMCoreSourceData.qPresentation,
    ``Physics.SMCoreSourceData.coloredPresentation,
    ``Physics.SMCoreSourceData.leptonPresentation,
    ``Physics.SMCoreSourceData.electronPresentation,
    ``Physics.SMCoreSourceData.conjugateQPresentation,
    ``Physics.SMCoreSourceData.conjugateColoredPresentation,
    ``Physics.SMCoreSourceData.conjugateLeptonPresentation,
    ``Physics.SMCoreSourceData.conjugateElectronPresentation,
    ``Physics.SMCoreSourceData.corePresentation,
    ``Physics.SMCoreSourceData.corePresentation_expression,
    ``Physics.SMJointSupportData.Index,
    ``Physics.SMJointSupportData.expressionData,
    ``Physics.SMJointSupportData.cores,
    ``Physics.SMJointSupportData.presentation,
    ``Physics.SMJointSupportData.DataSupport,
    ``Physics.SMJointSupportData.expressionData_eq,
    ``Physics.SMJointSupportData.dataSupport_presented_iff,
    ``Physics.SMJointSupportData.dataSupport_iff,
    ``Physics.SMJointSupportData.witness_to_original,
    ``Physics.SMJointSupportData.HiggsDataSupport,
    ``Physics.SMJointSupportData.higgsDataSupport_iff,
    ``Physics.SMJointSupportData.original_ql_iff,
    ``Physics.SMJointSupportDataExamples.component_to_support,
    ``Physics.SMJointSupportDataExamples.original_of_data,
    ``Physics.SMJointSupportDataExamples.mixedPattern,
    ``Physics.SMJointSupportDataExamples.mixed_allowed,
    ``Physics.SMJointSupportDataExamples.mixed_data_witness,
    ``Physics.SMJointSupportDataExamples.q18Pattern,
    ``Physics.SMJointSupportDataExamples.q18_allowed,
    ``Physics.SMJointSupportDataExamples.q18_data_witness,
    ``Physics.SMJointSupportDataExamples.oppositePair,
    ``Physics.SMJointSupportDataExamples.oppositePair_forbidden,
    ``Physics.SMJointSupportDataExamples.oppositePair_no_data]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM joint data audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM joint data: {ds.length} strict transitive checks passed"
