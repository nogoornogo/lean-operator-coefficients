import Physics.StandardModel.Operators.DevMohapatraHermitian
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Hermitian adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHermitian.vertex,
    ``GUT.DevMohapatraHermitian.scalarAction,
    ``GUT.DevMohapatraHermitian.leftSource,
    ``GUT.DevMohapatraHermitian.rightSource,
    ``GUT.DevMohapatraHermitian.complexifiedScalar,
    ``GUT.DevMohapatraHermitian.sources_conjugate,
    ``GUT.DevMohapatraHermitian.scalar_dictionary,
    ``GUT.DevMohapatraHermitian.scalar_hermitian,
    ``GUT.DevMohapatraHermitian.massAction,
    ``GUT.DevMohapatraHermitian.mass_hermitian,
    ``GUT.DevMohapatraHermitian.mass_dictionary,
    ``GUT.DevMohapatraHermitian.scalarEffective,
    ``GUT.DevMohapatraHermitian.scalar_on_shell,
    ``GUT.DevMohapatraHermitian.solutions_conjugate,
    ``GUT.DevMohapatraHermitian.hermitian_on_shell,
    ``GUT.DevMohapatraHermitian.effective_hermitian,
    ``GUT.DevMohapatraHermitian.effective_expansion,
    ``GUT.DevMohapatraHermitian.effective_projection,
    ``GUT.DevMohapatraHermitian.action,
    ``GUT.DevMohapatraHermitian.effectiveAction,
    ``GUT.DevMohapatraHermitian.action_hermitian,
    ``GUT.DevMohapatraHermitian.action_scalar_on_shell,
    ``GUT.DevMohapatraHermitian.action_effective_hermitian]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Hermitian adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Hermitian adapter: {ds.length} strict transitive checks passed"
