import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.Selection.BgwZ6Selection
import Physics.StandardModel.Operators.Weinberg.BgwChargedHiggsWeinberg

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "BGW selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.BgwChargedHiggsWeinberg.phase,
    ``Physics.BgwChargedHiggsWeinberg.lepton_scalar,
    ``Physics.BgwChargedHiggsWeinberg.higgs_scalar,
    ``Physics.BgwChargedHiggsWeinberg.phases,
    ``Physics.BgwChargedHiggsWeinberg.neutralEquiv,
    ``Physics.BgwChargedHiggsWeinberg.higgsEquiv,
    ``Physics.BgwChargedHiggsWeinberg.leptonEquiv,
    ``Physics.BgwChargedHiggsWeinberg.domainEquiv,
    ``Physics.BgwChargedHiggsWeinberg.coefficientEquiv,
    ``Physics.BgwChargedHiggsWeinberg.witness,
    ``Physics.BgwChargedHiggsWeinberg.witness_coordinate,
    ``Physics.BgwChargedHiggsWeinberg.witness_nonzero,
    ``Physics.BgwChargedHiggsWeinberg.exists_nonzero,

    ``Physics.BgwZ6Selection.fq,
    ``Physics.BgwZ6Selection.bq,
    ``Physics.BgwZ6Selection.fermion_identity,
    ``Physics.BgwZ6Selection.boson_identity,
    ``Physics.BgwZ6Selection.total,
    ``Physics.BgwZ6Selection.total_identity,
    ``Physics.BgwZ6Selection.copies,
    ``Physics.BgwZ6Selection.flavor,
    ``Physics.BgwZ6Selection.scalarFlavor,
    ``Physics.BgwZ6Selection.field_scalar,
    ``Physics.BgwZ6Selection.scalar_scalar,
    ``Physics.BgwZ6Selection.charge_of_nonzero,
    ``Physics.BgwZ6Selection.baryon_divisible,
    ``Physics.BgwZ6Selection.forbidden_values,
    ``Physics.BgwZ6Selection.all_forbidden,
    ``Physics.BgwZ6Selection.residual_forbidden,
    ``Physics.BgwZ6Selection.printed_dictionary,
    ``Physics.BgwZ6Selection.fermion_conjugates,
    ``Physics.BgwZ6Selection.higgs_conjugates,
    ``Physics.BgwZ6Selection.llhh_neutral]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "BGW selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"BGW Z6: {ds.length} strict transitive checks passed"
