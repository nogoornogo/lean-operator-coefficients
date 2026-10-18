import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.BgwZ6Selection
import Physics.StandardModel.Operators.BgwChargedHiggsWeinberg

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "BGW selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``GUT.BgwChargedHiggsWeinberg.phase,
    ``GUT.BgwChargedHiggsWeinberg.lepton_scalar,
    ``GUT.BgwChargedHiggsWeinberg.higgs_scalar,
    ``GUT.BgwChargedHiggsWeinberg.phases,
    ``GUT.BgwChargedHiggsWeinberg.neutralEquiv,
    ``GUT.BgwChargedHiggsWeinberg.higgsEquiv,
    ``GUT.BgwChargedHiggsWeinberg.leptonEquiv,
    ``GUT.BgwChargedHiggsWeinberg.domainEquiv,
    ``GUT.BgwChargedHiggsWeinberg.coefficientEquiv,
    ``GUT.BgwChargedHiggsWeinberg.witness,
    ``GUT.BgwChargedHiggsWeinberg.witness_coordinate,
    ``GUT.BgwChargedHiggsWeinberg.witness_nonzero,
    ``GUT.BgwChargedHiggsWeinberg.exists_nonzero,

    ``GUT.BgwZ6Selection.fq,
    ``GUT.BgwZ6Selection.bq,
    ``GUT.BgwZ6Selection.fermion_identity,
    ``GUT.BgwZ6Selection.boson_identity,
    ``GUT.BgwZ6Selection.total,
    ``GUT.BgwZ6Selection.total_identity,
    ``GUT.BgwZ6Selection.copies,
    ``GUT.BgwZ6Selection.flavor,
    ``GUT.BgwZ6Selection.scalarFlavor,
    ``GUT.BgwZ6Selection.field_scalar,
    ``GUT.BgwZ6Selection.scalar_scalar,
    ``GUT.BgwZ6Selection.charge_of_nonzero,
    ``GUT.BgwZ6Selection.baryon_divisible,
    ``GUT.BgwZ6Selection.forbidden_values,
    ``GUT.BgwZ6Selection.all_forbidden,
    ``GUT.BgwZ6Selection.residual_forbidden,
    ``GUT.BgwZ6Selection.printed_dictionary,
    ``GUT.BgwZ6Selection.fermion_conjugates,
    ``GUT.BgwZ6Selection.higgs_conjugates,
    ``GUT.BgwZ6Selection.llhh_neutral]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "BGW selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"BGW Z6: {ds.length} strict transitive checks passed"
