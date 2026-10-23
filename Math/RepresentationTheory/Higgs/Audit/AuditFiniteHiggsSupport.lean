import Math.RepresentationTheory.Higgs.BoundedHiggsSupport
import Math.RepresentationTheory.Coefficients.PatternCoefficientSupport
import Math.RepresentationTheory.Tensors.InvariantTensorCharge
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite Higgs support imports application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.BoundedTorusWeights.of_basis,
    ``Math.BoundedTorusWeights.dual_basis_eigen,
    ``Math.BoundedTorusWeights.eigen_tmul,
    ``Math.BoundedTorusWeights.bounded_of_surjective,
    ``Math.BoundedTorusWeights.eigen_pair_zero,
    ``Math.BoundedTorusWeights.dual_eigen_zero,
    ``Math.BoundedTorusWeights.high_spin_hom_zero,
    ``Math.PatternExteriorSource.map,
    ``Math.PatternExteriorSource.orbit_iff_counts,
    ``Math.PatternExteriorSource.onto,
    ``Math.PatternExteriorSource.onto_surjective,
    ``Math.PatternExteriorSource.source_scalar,
    ``Math.PatternExteriorSource.inclusion,
    ``Math.PatternExteriorSource.onto_tprod,
    ``Math.PatternExteriorSource.pure_val,
    ``Math.PatternExteriorSource.pure_compatible,
    ``Math.PatternExteriorSource.projectionLinear,
    ``Math.PatternExteriorSource.projection_pure,
    ``Math.PatternExteriorSource.projection_vanish,
    ``Math.PatternExteriorSource.projection_inclusion,
    ``Math.PatternExteriorSource.pure_action,
    ``Math.PatternExteriorSource.projection,
    ``Math.PatternCoefficientSupport.restrict,
    ``Math.PatternCoefficientSupport.extend,
    ``Math.PatternCoefficientSupport.restrict_extend,
    ``Math.PatternCoefficientSupport.extend_supported,
    ``Math.PatternCoefficientSupport.pure_ext,
    ``Math.PatternCoefficientSupport.pattern_ext,
    ``Math.PatternCoefficientSupport.extend_restrict,
    ``Math.PatternCoefficientSupport.equiv,
    ``Math.FiniteConstituentSupport.restrict,
    ``Math.FiniteConstituentSupport.extend,
    ``Math.FiniteConstituentSupport.restrict_extend,
    ``Math.FiniteConstituentSupport.eq_zero_of_restrict,
    ``Math.FiniteConstituentSupport.allowed_iff,
    ``Math.BoundedHiggsSupport.constituent_weak,
    ``Math.BoundedHiggsSupport.weakCurry,
    ``Math.BoundedHiggsSupport.high_zero,
    ``Math.BoundedHiggsSupport.charge_eq,
    ``Math.BoundedHiggsSupport.summandEquiv,
    ``Math.BoundedHiggsSupport.per_degree_allowed,
    ``Math.BoundedHiggsSupport.degree_admissible,
    ``Math.BoundedHiggsSupport.exists_index,
    ``Math.BoundedHiggsSupport.finite_allowed_iff,
    ``Math.BoundedHiggsSupport.admissible_pair,
    ``Math.BoundedHiggsSupport.admissible_stable,
    ``Math.BoundedHiggsSupport.pair_monotone,
    ``Math.BoundedHiggsSupport.pair_stable,
    ``Math.BoundedHiggsSupport.finite_table_iff,
    ``Math.BoundedHiggsSupport.imbalance_forbidden,
    ``Math.BoundedHiggsSupport.pair_stable_at_threshold,
    ``Math.BoundedHiggsSupport.representativeEquiv,
    ``Math.BoundedHiggsSupport.constituentCast,
    ``Math.BoundedHiggsSupport.pairs_stable,
    ``Math.InvariantTensorCharge.charge_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite Higgs support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite Higgs support Math: layer and {ds.length} strict transitive axiom checks passed"
