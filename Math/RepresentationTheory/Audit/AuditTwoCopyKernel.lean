import Math.RepresentationTheory.Decomposition.TwoCopyKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``TwoCopyKernel.sector, ``TwoCopyKernel.solve,
    ``TwoCopyKernel.ofRight, ``TwoCopyKernel.swap, ``TwoCopyKernel.ofNonzero,
    ``TwoCopyKernel.ofZero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-copy kernel: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-copy kernel: {declarations.length} strict axiom checks passed"
