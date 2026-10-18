import Physics.StandardModel.Gauge.TwistedFundamentalIrreducibility
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.StandardSMIrreducibility.twisted_color_irreducible,
    ``GUT.StandardSMIrreducibility.twisted_weak_irreducible,
    ``GUT.StandardSMIrreducibility.twisted_color_dual_irreducible,
    ``GUT.StandardSMIrreducibility.twisted_weak_dual_irreducible,
    ``GUT.StandardSMIrreducibility.neutral_extension_irreducible]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Twisted fundamental: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Twisted fundamental: {declarations.length} strict axiom checks passed"
