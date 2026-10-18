import Physics.StandardModel.Operators.DevMohapatraParity
import Physics.StandardModel.Operators.DevMohapatraSixQuark
import Physics.StandardModel.Operators.MaZ3Mixed
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-SUSY mixed imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraParity.H,
    ``GUT.DevMohapatraParity.chi,
    ``GUT.DevMohapatraParity.copies,
    ``GUT.DevMohapatraParity.flavor,
    ``GUT.DevMohapatraParity.scalarFlavor,
    ``GUT.DevMohapatraParity.detect,
    ``GUT.DevMohapatraParity.all_bOne_forbidden,
    ``GUT.DevMohapatraParity.lepton_trivial,
    ``GUT.DevMohapatraParity.higgs_trivial,
    ``GUT.DevMohapatraParity.LLHH,
    ``GUT.DevMohapatraParity.llhh_allowed,
    ``GUT.DevMohapatraSixQuark.F,
    ``GUT.DevMohapatraSixQuark.H,
    ``GUT.DevMohapatraSixQuark.residual,
    ``GUT.DevMohapatraSixQuark.Sector,
    ``GUT.DevMohapatraSixQuark.project,
    ``GUT.DevMohapatraSixQuark.project_pure,
    ``GUT.DevMohapatraSixQuark.project_natural,
    ``GUT.DevMohapatraSixQuark.phase,
    ``GUT.DevMohapatraSixQuark.phase_six,
    ``GUT.DevMohapatraSixQuark.project_residual,
    ``GUT.DevMohapatraSixQuark.liftCoefficient,
    ``GUT.DevMohapatraSixQuark.labels,
    ``GUT.DevMohapatraSixQuark.lift_selected,
    ``GUT.DevMohapatraSixQuark.selected_nonzero,
    ``GUT.DevMohapatraSixQuark.allowed,
    ``GUT.DevMohapatraSixQuark.Target,
    ``GUT.DevMohapatraSixQuark.domain,
    ``GUT.DevMohapatraSixQuark.request,
    ``GUT.DevMohapatraSixQuark.satisfies,
    ``GUT.MaZ3Mixed.H,
    ``GUT.MaZ3Mixed.P,
    ``GUT.MaZ3Mixed.phase,
    ``GUT.MaZ3Mixed.compensated,
    ``GUT.MaZ3Mixed.neutrino,
    ``GUT.MaZ3Mixed.scalar,
    ``GUT.MaZ3Mixed.scalar_action,
    ``GUT.MaZ3Mixed.epsilonExterior,
    ``GUT.MaZ3Mixed.epsilonExterior_apply,
    ``GUT.MaZ3Mixed.epsilon_neutrino,
    ``GUT.MaZ3Mixed.Bare,
    ``GUT.MaZ3Mixed.Dressed,
    ``GUT.MaZ3Mixed.dressed,
    ``GUT.MaZ3Mixed.dressed_evaluation,
    ``GUT.MaZ3Mixed.dressed_nonzero,
    ``GUT.MaZ3Mixed.exists_dressed,
    ``GUT.MaZ3Mixed.detector,
    ``GUT.MaZ3Mixed.detector_square,
    ``GUT.MaZ3Mixed.bare_forbidden,
    ``GUT.MaZ3Mixed.Target,
    ``GUT.MaZ3Mixed.domain,
    ``GUT.MaZ3Mixed.request,
    ``GUT.MaZ3Mixed.satisfies]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-SUSY mixed: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-SUSY mixed: {ds.length} strict transitive checks passed"
