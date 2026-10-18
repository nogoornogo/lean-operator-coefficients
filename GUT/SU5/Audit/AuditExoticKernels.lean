import GUT.SU5.Representations.ExoticSymmetricKernel
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.ExoticWedgeKernel.wedgeMap,
    ``GUT.SU5.ExoticWedgeKernel.wedge_surjective,
    ``GUT.SU5.ExoticWedgeKernel.kernel_finrank,
    ``GUT.SU5.ExoticWedgeKernel.representation_finrank,
    ``GUT.SU5.ExoticWedgeKernel.kernel_character,
    ``GUT.SU5.ExoticWedgeKernel.representation_character,
    ``GUT.SU5.ExoticSymmetricKernel.product_comm,
    ``GUT.SU5.ExoticSymmetricKernel.product_covariant,
    ``GUT.SU5.ExoticSymmetricKernel.wedgeMap,
    ``GUT.SU5.ExoticSymmetricKernel.wedge_surjective,
    ``GUT.SU5.ExoticSymmetricKernel.kernel_finrank,
    ``GUT.SU5.ExoticSymmetricKernel.kernel_character]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Actual exotic kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Actual exotic kernels: {ds.length} strict transitive checks passed"
