import Math.RepresentationTheory.SU2.SL2ClebschGordan
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "SL2 Clebsch–Gordan audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SL2SymmetricEmbeddings.omega_invariant,
    ``Math.SL2SymmetricEmbeddings.omegaPower_eq,
    ``Math.SL2SymmetricEmbeddings.embedding_linearMap,
    ``Math.SL2SymmetricEmbeddings.embedding_injective,
    ``Math.SL2SymmetricEmbeddings.symmetricPower_compact,
    ``Math.SL2SymmetricEmbeddings.coefficient_fixed_of_compact,
    ``Math.SL2ClebschGordan.embed_linearMap,
    ``Math.SL2ClebschGordan.assemble_linearMap,
    ``Math.SL2ClebschGordan.equivalence,
    ``Math.SL2ClebschGordan.coefficient_fixed_of_compact]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SL2 Clebsch–Gordan audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SL2 Clebsch–Gordan: layer and {ds.length} strict transitive checks passed"
