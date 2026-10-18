import GUT.SU6.SelectionRules.Models.FiniteIndexCertificate
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU6FiniteIndexCertificate.Label,
    ``GUT.SU6FiniteIndexCertificate.branching, ``GUT.SU6FiniteIndexCertificate.rows,
    ``GUT.SU6FiniteIndexCertificate.conjugate, ``GUT.SU6FiniteIndexCertificate.column,
    ``GUT.SU6FiniteIndexCertificate.certificate, ``GUT.SU6FiniteIndexCertificate.target,
    ``GUT.SU6FiniteIndexCertificate.lightProfile, ``GUT.SU6FiniteIndexCertificate.negateRow,
    ``GUT.SU6FiniteIndexCertificate.target_dictionary,
    ``GUT.SU6FiniteIndexCertificate.annihilates, ``GUT.SU6FiniteIndexCertificate.separates,
    ``GUT.SU6FiniteIndexCertificate.no_solution, ``GUT.SU6FiniteIndexCertificate.Admitted,
    ``GUT.SU6FiniteIndexCertificate.not_admitted,
    ``GUT.SU6FiniteIndexCertificate.no_integer_solution,
    ``GUT.SU6FiniteIndexCertificate.doubletDifference,
    ``GUT.SU6FiniteIndexCertificate.tripletBalance,
    ``GUT.SU6FiniteIndexCertificate.chargedDifference,
    ``GUT.SU6FiniteIndexCertificate.multiplicity,
    ``GUT.SU6FiniteIndexCertificate.doublet_count,
    ``GUT.SU6FiniteIndexCertificate.conjugate_count,
    ``GUT.SU6FiniteIndexCertificate.balance_count,
    ``GUT.SU6FiniteIndexCertificate.row0_eq_row2,
    ``GUT.SU6FiniteIndexCertificate.row5_eq_row6,
    ``GUT.SU6FiniteIndexCertificate.row_balance,
    ``GUT.SU6FiniteIndexCertificate.zero_neg_charge,
    ``GUT.SU6FiniteIndexCertificate.response,
    ``GUT.SU6FiniteIndexCertificate.certificate_response]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite index: {ds.length} strict transitive checks passed"
