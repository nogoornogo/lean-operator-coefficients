import Physics.FieldTheory.Spinor.Weyl.WeylFiniteKernelControl
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``Physics.WeylGeneratorTests.generates,
    ``Physics.WeylGeneratorTests.invariant_iff,
    ``Physics.WeylFiniteKernelControl.upper,
    ``Physics.WeylFiniteKernelControl.lower,
    ``Physics.WeylFiniteKernelControl.tests_force_zero,
    ``Physics.WeylFiniteKernelControl.exhaustive,
    ``Physics.WeylFiniteKernelControl.coefficientEquiv,
    ``Physics.WeylFiniteKernelControl.kernel_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weyl kernel tests: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weyl kernel tests: {ds.length} strict transitive axiom checks passed"
