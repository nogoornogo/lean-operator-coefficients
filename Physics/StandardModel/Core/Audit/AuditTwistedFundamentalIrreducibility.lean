import Physics.StandardModel.Gauge.Tensors.TwistedFundamentalIrreducibility
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``Physics.StandardSMIrreducibility.twisted_color_irreducible,
    ``Physics.StandardSMIrreducibility.twisted_weak_irreducible,
    ``Physics.StandardSMIrreducibility.twisted_color_dual_irreducible,
    ``Physics.StandardSMIrreducibility.twisted_weak_dual_irreducible,
    ``Physics.StandardSMIrreducibility.neutral_extension_irreducible]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Twisted fundamental: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Twisted fundamental: {declarations.length} strict axiom checks passed"
