import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraParity
import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraSixQuark
import Physics.StandardModel.Operators.Selection.MaZ3Mixed
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-SUSY mixed imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraParity.H,
    ``Physics.DevMohapatraParity.chi,
    ``Physics.DevMohapatraParity.copies,
    ``Physics.DevMohapatraParity.flavor,
    ``Physics.DevMohapatraParity.scalarFlavor,
    ``Physics.DevMohapatraParity.detect,
    ``Physics.DevMohapatraParity.all_bOne_forbidden,
    ``Physics.DevMohapatraParity.lepton_trivial,
    ``Physics.DevMohapatraParity.higgs_trivial,
    ``Physics.DevMohapatraParity.LLHH,
    ``Physics.DevMohapatraParity.llhh_allowed,
    ``Physics.DevMohapatraSixQuark.F,
    ``Physics.DevMohapatraSixQuark.H,
    ``Physics.DevMohapatraSixQuark.residual,
    ``Physics.DevMohapatraSixQuark.Sector,
    ``Physics.DevMohapatraSixQuark.project,
    ``Physics.DevMohapatraSixQuark.project_pure,
    ``Physics.DevMohapatraSixQuark.project_natural,
    ``Physics.DevMohapatraSixQuark.phase,
    ``Physics.DevMohapatraSixQuark.phase_six,
    ``Physics.DevMohapatraSixQuark.project_residual,
    ``Physics.DevMohapatraSixQuark.liftCoefficient,
    ``Physics.DevMohapatraSixQuark.labels,
    ``Physics.DevMohapatraSixQuark.lift_selected,
    ``Physics.DevMohapatraSixQuark.selected_nonzero,
    ``Physics.DevMohapatraSixQuark.allowed,
    ``Physics.DevMohapatraSixQuark.Target,
    ``Physics.DevMohapatraSixQuark.domain,
    ``Physics.DevMohapatraSixQuark.request,
    ``Physics.DevMohapatraSixQuark.satisfies,
    ``Physics.MaZ3Mixed.H,
    ``Physics.MaZ3Mixed.P,
    ``Physics.MaZ3Mixed.phase,
    ``Physics.MaZ3Mixed.compensated,
    ``Physics.MaZ3Mixed.neutrino,
    ``Physics.MaZ3Mixed.scalar,
    ``Physics.MaZ3Mixed.scalar_action,
    ``Physics.MaZ3Mixed.epsilonExterior,
    ``Physics.MaZ3Mixed.epsilonExterior_apply,
    ``Physics.MaZ3Mixed.epsilon_neutrino,
    ``Physics.MaZ3Mixed.Bare,
    ``Physics.MaZ3Mixed.Dressed,
    ``Physics.MaZ3Mixed.dressed,
    ``Physics.MaZ3Mixed.dressed_evaluation,
    ``Physics.MaZ3Mixed.dressed_nonzero,
    ``Physics.MaZ3Mixed.exists_dressed,
    ``Physics.MaZ3Mixed.detector,
    ``Physics.MaZ3Mixed.detector_square,
    ``Physics.MaZ3Mixed.bare_forbidden,
    ``Physics.MaZ3Mixed.Target,
    ``Physics.MaZ3Mixed.domain,
    ``Physics.MaZ3Mixed.request,
    ``Physics.MaZ3Mixed.satisfies]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-SUSY mixed: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-SUSY mixed: {ds.length} strict transitive checks passed"
