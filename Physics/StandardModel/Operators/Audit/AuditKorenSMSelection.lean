import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.KorenSMSelection

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Koren selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``GUT.KorenSMSelection.embedding,
    ``GUT.KorenSMSelection.embedding_injective,
    ``GUT.KorenSMSelection.chi,
    ``GUT.KorenSMSelection.chi_restriction,
    ``GUT.KorenSMSelection.chi_mul,
    ``GUT.KorenSMSelection.target,
    ``GUT.KorenSMSelection.target_union,
    ``GUT.KorenSMSelection.neutral_iff,
    ``GUT.KorenSMSelection.baryon_divisible,
    ``GUT.KorenSMSelection.detect,
    ``GUT.KorenSMSelection.copies,
    ``GUT.KorenSMSelection.flavor,
    ``GUT.KorenSMSelection.scalarFlavor,
    ``GUT.KorenSMSelection.all_forbidden,
    ``GUT.KorenSMSelection.residual_forbidden,
    ``GUT.KorenSMSelection.printed_dictionary,
    ``GUT.KorenSMSelection.fermion_conjugates,
    ``GUT.KorenSMSelection.higgs_neutral,
    ``GUT.KorenSMSelection.llhh_detect]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Koren selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Koren SM: {ds.length} strict transitive checks passed"
