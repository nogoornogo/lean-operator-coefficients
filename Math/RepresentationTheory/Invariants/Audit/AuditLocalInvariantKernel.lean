import Math.RepresentationTheory.Invariants.PolynomialInvariantTests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Local invariant kernel imports application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.FiniteInvariantKernel.coordinates,
    ``Math.FiniteInvariantKernel.coordinates_apply,
    ``Math.FiniteInvariantKernel.constraints_apply,
    ``Math.FiniteInvariantKernel.mem_kernel_iff,
    ``Math.FiniteInvariantKernel.equiv,
    ``Math.FiniteInvariantKernel.allowed_iff,
    ``Math.FiniteInvariantKernel.allowed_iff_rank_lt,
    ``Math.GeneratorInvariantTests.fixing,
    ``Math.GeneratorInvariantTests.invariant_iff,
    ``Math.GeneratorInvariantTests.exhaustive,
    ``Math.PolynomialInvariantTests.zero_of_samples,
    ``Math.PolynomialInvariantTests.grid_zero,
    ``Math.PolynomialInvariantTests.exhaustive]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Local invariant kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Local invariant kernel: layer and {ds.length} strict transitive axiom checks passed"
