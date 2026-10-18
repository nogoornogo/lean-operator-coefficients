import Physics.StandardModel.Operators.SMConstantSourceCharacter
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM source character audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMConstantSourceCharacter.weak_character,
    ``GUT.SMConstantSourceCharacter.lepton_generating,
    ``GUT.SMConstantSourceCharacter.lepton_weak_character,
    ``GUT.SMConstantSourceCharacter.left_torus_basis,
    ``GUT.SMConstantSourceCharacter.lepton_basis_eigen,
    ``GUT.SMConstantSourceCharacter.lepton_character,
    ``GUT.SMConstantSourceCharacter.lepton_pair_generating,
    ``GUT.SMConstantSourceCharacter.lepton_character_product]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM source character audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM source characters: layer and {ds.length} strict transitive checks passed"
