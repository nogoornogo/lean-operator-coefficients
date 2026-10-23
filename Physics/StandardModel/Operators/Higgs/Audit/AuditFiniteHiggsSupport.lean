import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteSupportTable
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [
    ``Physics.SMWeakWeightBasis.weak_basis_eigen,
    ``Physics.SMWeakWeightBasis.color_basis_eigen,
    ``Physics.SMWeakWeightBasis.twist_eigen,
    ``Physics.SMWeakWeightBasis.gauge_basis_eigen,
    ``Physics.SMWeakWeightBasis.gauge_weight_bound,
    ``Physics.SMWeakWeightBasis.field_basis_eigen,
    ``Physics.SMWeakWeightBasis.field_bounded,
    ``Physics.SMContentWeakBound.tensor_basis_eigen,
    ``Physics.SMContentWeakBound.tensor_weight_bound,
    ``Physics.SMContentWeakBound.raw_bounded,
    ``Physics.SMContentWeakBound.source_bounded,
    ``Physics.SMContentWeakBound.source_dual_eigen_zero,
    ``Physics.SMContentWeakBound.bound_le_degree,
    ``Physics.SMContentWeakBound.pilot_bound,
    ``Physics.SMContentWeakBound.raw_hypercharge,
    ``Physics.SMContentWeakBound.source_hypercharge,
    ``Physics.SMFiniteHiggsSupport.weak_projection,
    ``Physics.SMFiniteHiggsSupport.weak_character,
    ``Physics.SMFiniteHiggsSupport.source_bound,
    ``Physics.SMFiniteHiggsSupport.split_allowed,
    ``Physics.SMFiniteHiggsSupport.finite_allowed_iff,
    ``Physics.SMFiniteHiggsSupport.originalEquiv,
    ``Physics.SMFiniteHiggsSupport.mem_original_iff,
    ``Physics.SMFiniteHiggsSupport.original_allowed_iff,
    ``Physics.SMFiniteHiggsSupport.original_table_iff,
    ``Physics.SMFiniteHiggsSupport.original_pair_monotone,
    ``Physics.SMFiniteHiggsSupport.original_pair_stable,
    ``Physics.SMFiniteHiggsSupport.original_imbalance_forbidden,
    ``Physics.SMFiniteHiggsSupport.original_degree_forbidden,
    ``Physics.SMFiniteHiggsSupport.constituent_hypercharge,
    ``Physics.SMFiniteHiggsSupport.test_charge,
    ``Physics.SMFiniteHiggsSupport.original_charge_finite_iff,
    ``Physics.SMFiniteHiggsSupport.original_forbidden_iff,
    ``Physics.SMFiniteHiggsSupport.original_pairs_stable,
    ``Physics.SMFiniteSupportTable.finite_universe_iff,
    ``Physics.SMFiniteSupportTable.all_degrees_iff,
    ``Physics.SMFiniteSupportTable.global_table_iff,
    ``Physics.SMFiniteSupportTable.pilot_all_forbidden,
    ``Physics.SMFiniteSupportTable.family_bound_controls,
    ``Physics.SMFiniteSupportTable.family_charge_controls]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM finite Higgs support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM finite Higgs support: {ds.length} strict transitive axiom checks passed"
