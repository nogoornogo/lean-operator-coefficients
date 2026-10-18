import Physics.StandardModel.Operators.SMFiniteSupportTable
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [
    ``GUT.SMWeakWeightBasis.weak_basis_eigen,
    ``GUT.SMWeakWeightBasis.color_basis_eigen,
    ``GUT.SMWeakWeightBasis.twist_eigen,
    ``GUT.SMWeakWeightBasis.gauge_basis_eigen,
    ``GUT.SMWeakWeightBasis.gauge_weight_bound,
    ``GUT.SMWeakWeightBasis.field_basis_eigen,
    ``GUT.SMWeakWeightBasis.field_bounded,
    ``GUT.SMContentWeakBound.tensor_basis_eigen,
    ``GUT.SMContentWeakBound.tensor_weight_bound,
    ``GUT.SMContentWeakBound.raw_bounded,
    ``GUT.SMContentWeakBound.source_bounded,
    ``GUT.SMContentWeakBound.source_dual_eigen_zero,
    ``GUT.SMContentWeakBound.bound_le_degree,
    ``GUT.SMContentWeakBound.pilot_bound,
    ``GUT.SMContentWeakBound.raw_hypercharge,
    ``GUT.SMContentWeakBound.source_hypercharge,
    ``GUT.SMFiniteHiggsSupport.weak_projection,
    ``GUT.SMFiniteHiggsSupport.weak_character,
    ``GUT.SMFiniteHiggsSupport.source_bound,
    ``GUT.SMFiniteHiggsSupport.split_allowed,
    ``GUT.SMFiniteHiggsSupport.finite_allowed_iff,
    ``GUT.SMFiniteHiggsSupport.originalEquiv,
    ``GUT.SMFiniteHiggsSupport.mem_original_iff,
    ``GUT.SMFiniteHiggsSupport.original_allowed_iff,
    ``GUT.SMFiniteHiggsSupport.original_table_iff,
    ``GUT.SMFiniteHiggsSupport.original_pair_monotone,
    ``GUT.SMFiniteHiggsSupport.original_pair_stable,
    ``GUT.SMFiniteHiggsSupport.original_imbalance_forbidden,
    ``GUT.SMFiniteHiggsSupport.original_degree_forbidden,
    ``GUT.SMFiniteHiggsSupport.constituent_hypercharge,
    ``GUT.SMFiniteHiggsSupport.test_charge,
    ``GUT.SMFiniteHiggsSupport.original_charge_finite_iff,
    ``GUT.SMFiniteHiggsSupport.original_forbidden_iff,
    ``GUT.SMFiniteHiggsSupport.original_pairs_stable,
    ``GUT.SMFiniteSupportTable.finite_universe_iff,
    ``GUT.SMFiniteSupportTable.all_degrees_iff,
    ``GUT.SMFiniteSupportTable.global_table_iff,
    ``GUT.SMFiniteSupportTable.pilot_all_forbidden,
    ``GUT.SMFiniteSupportTable.family_bound_controls,
    ``GUT.SMFiniteSupportTable.family_charge_controls]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM finite Higgs support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM finite Higgs support: {ds.length} strict transitive axiom checks passed"
