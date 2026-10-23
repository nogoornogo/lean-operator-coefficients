import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.Selection.KorenSMSelection

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Koren selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.KorenSMSelection.embedding,
    ``Physics.KorenSMSelection.embedding_injective,
    ``Physics.KorenSMSelection.chi,
    ``Physics.KorenSMSelection.chi_restriction,
    ``Physics.KorenSMSelection.chi_mul,
    ``Physics.KorenSMSelection.target,
    ``Physics.KorenSMSelection.target_union,
    ``Physics.KorenSMSelection.neutral_iff,
    ``Physics.KorenSMSelection.baryon_divisible,
    ``Physics.KorenSMSelection.detect,
    ``Physics.KorenSMSelection.copies,
    ``Physics.KorenSMSelection.flavor,
    ``Physics.KorenSMSelection.scalarFlavor,
    ``Physics.KorenSMSelection.all_forbidden,
    ``Physics.KorenSMSelection.residual_forbidden,
    ``Physics.KorenSMSelection.printed_dictionary,
    ``Physics.KorenSMSelection.fermion_conjugates,
    ``Physics.KorenSMSelection.higgs_neutral,
    ``Physics.KorenSMSelection.llhh_detect]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Koren selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Koren SM: {ds.length} strict transitive checks passed"
