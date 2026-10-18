import Math.RepresentationTheory.Audit.AuditJointSourceReexpression
import Physics.StandardModel.Operators.SMJointSupportDataExamples
run_cmd do
  let ds := [
    ``GUT.SMCoreSourceData.coreData,
    ``GUT.SMCoreSourceData.qPresentation,
    ``GUT.SMCoreSourceData.coloredPresentation,
    ``GUT.SMCoreSourceData.leptonPresentation,
    ``GUT.SMCoreSourceData.electronPresentation,
    ``GUT.SMCoreSourceData.conjugateQPresentation,
    ``GUT.SMCoreSourceData.conjugateColoredPresentation,
    ``GUT.SMCoreSourceData.conjugateLeptonPresentation,
    ``GUT.SMCoreSourceData.conjugateElectronPresentation,
    ``GUT.SMCoreSourceData.corePresentation,
    ``GUT.SMCoreSourceData.corePresentation_expression,
    ``GUT.SMJointSupportData.Index,
    ``GUT.SMJointSupportData.expressionData,
    ``GUT.SMJointSupportData.cores,
    ``GUT.SMJointSupportData.presentation,
    ``GUT.SMJointSupportData.DataSupport,
    ``GUT.SMJointSupportData.expressionData_eq,
    ``GUT.SMJointSupportData.dataSupport_presented_iff,
    ``GUT.SMJointSupportData.dataSupport_iff,
    ``GUT.SMJointSupportData.witness_to_original,
    ``GUT.SMJointSupportData.HiggsDataSupport,
    ``GUT.SMJointSupportData.higgsDataSupport_iff,
    ``GUT.SMJointSupportData.original_ql_iff,
    ``GUT.SMJointSupportDataExamples.component_to_support,
    ``GUT.SMJointSupportDataExamples.original_of_data,
    ``GUT.SMJointSupportDataExamples.mixedPattern,
    ``GUT.SMJointSupportDataExamples.mixed_allowed,
    ``GUT.SMJointSupportDataExamples.mixed_data_witness,
    ``GUT.SMJointSupportDataExamples.q18Pattern,
    ``GUT.SMJointSupportDataExamples.q18_allowed,
    ``GUT.SMJointSupportDataExamples.q18_data_witness,
    ``GUT.SMJointSupportDataExamples.oppositePair,
    ``GUT.SMJointSupportDataExamples.oppositePair_forbidden,
    ``GUT.SMJointSupportDataExamples.oppositePair_no_data]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM joint data audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM joint data: {ds.length} strict transitive checks passed"
