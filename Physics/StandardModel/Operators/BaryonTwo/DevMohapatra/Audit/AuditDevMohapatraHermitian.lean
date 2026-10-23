import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHermitian
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Hermitian adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHermitian.vertex,
    ``Physics.DevMohapatraHermitian.scalarAction,
    ``Physics.DevMohapatraHermitian.leftSource,
    ``Physics.DevMohapatraHermitian.rightSource,
    ``Physics.DevMohapatraHermitian.complexifiedScalar,
    ``Physics.DevMohapatraHermitian.sources_conjugate,
    ``Physics.DevMohapatraHermitian.scalar_dictionary,
    ``Physics.DevMohapatraHermitian.scalar_hermitian,
    ``Physics.DevMohapatraHermitian.massAction,
    ``Physics.DevMohapatraHermitian.mass_hermitian,
    ``Physics.DevMohapatraHermitian.mass_dictionary,
    ``Physics.DevMohapatraHermitian.scalarEffective,
    ``Physics.DevMohapatraHermitian.scalar_on_shell,
    ``Physics.DevMohapatraHermitian.solutions_conjugate,
    ``Physics.DevMohapatraHermitian.hermitian_on_shell,
    ``Physics.DevMohapatraHermitian.effective_hermitian,
    ``Physics.DevMohapatraHermitian.effective_expansion,
    ``Physics.DevMohapatraHermitian.effective_projection,
    ``Physics.DevMohapatraHermitian.action,
    ``Physics.DevMohapatraHermitian.effectiveAction,
    ``Physics.DevMohapatraHermitian.action_hermitian,
    ``Physics.DevMohapatraHermitian.action_scalar_on_shell,
    ``Physics.DevMohapatraHermitian.action_effective_hermitian]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Hermitian adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Hermitian adapter: {ds.length} strict transitive checks passed"
