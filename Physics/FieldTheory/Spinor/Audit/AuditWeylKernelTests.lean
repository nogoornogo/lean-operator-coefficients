import Physics.FieldTheory.Spinor.WeylFiniteKernelControl
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.WeylGeneratorTests.generates,
    ``GUT.WeylGeneratorTests.invariant_iff,
    ``GUT.WeylFiniteKernelControl.upper,
    ``GUT.WeylFiniteKernelControl.lower,
    ``GUT.WeylFiniteKernelControl.tests_force_zero,
    ``GUT.WeylFiniteKernelControl.exhaustive,
    ``GUT.WeylFiniteKernelControl.coefficientEquiv,
    ``GUT.WeylFiniteKernelControl.kernel_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weyl kernel tests: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weyl kernel tests: {ds.length} strict transitive axiom checks passed"
