import Math.RepresentationTheory.Multiplicity.MultiplicityDuality
import Math.RepresentationTheory.Multiplicity.MultiplicityTransport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Multiplicity duality imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.IntertwinerTraceDuality.transposeEquiv,
    ``Math.IntertwinerTraceDuality.pairing_bijective,
    ``Math.IntertwinerTraceDuality.equiv,
    ``Math.MultiplicityDuality.reverse_action,
    ``Math.MultiplicityDuality.equiv,
    ``Math.MultiplicityTransport.target,
    ``Math.MultiplicityTransport.source,
    ``Math.MultiplicityTransport.prod]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Multiplicity duality: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Multiplicity duality: {declarations.length} strict axiom checks passed"
