import Math.RepresentationTheory.SixSlotSpeciesTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.SixSlotSpeciesTransport.scaling_commutes,
    ``Math.SixSlotSpeciesTransport.pull_mem,
    ``Math.SixSlotSpeciesTransport.pull_symm,
    ``Math.SixSlotSpeciesTransport.equiv,
    ``Math.SixSlotSpeciesTransport.exists_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-slot transport audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-slot transport audit: {declarations.length} strict checks passed"
