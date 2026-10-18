import GUT.SU5.Branching.FortyElectronExclusion
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.SU5.WedgeKernelProjection.wedge_section,
    ``GUT.SU5.WedgeKernelProjection.section_pure,
    ``GUT.SU5.WedgeKernelProjection.sectionMap,
    ``GUT.SU5.WedgeKernelProjection.wedge_projection,
    ``GUT.SU5.WedgeKernelProjection.projection_on_kernel,
    ``GUT.SU5.FortySelectedCopies.kernelProjection,
    ``GUT.SU5.FortySelectedCopies.up_probe_projection,
    ``GUT.SU5.FortySelectedCopies.quark_probe_projection,
    ``GUT.SU5.FortySelectedCopies.upSourceEquiv,
    ``GUT.SU5.FortySelectedCopies.quarkSourceEquiv,
    ``GUT.SU5.FortySelectedCopies.upKernelProbe_ne_zero,
    ``GUT.SU5.FortySelectedCopies.quarkKernelProbe_ne_zero,
    ``GUT.SU5.FortySelectedCopies.upCopy_ne_zero,
    ``GUT.SU5.FortySelectedCopies.quarkCopy_ne_zero,
    ``GUT.SU5.FortySelectedCopies.selected_positive_multiplicities,
    ``GUT.SU5.FortyElectronExclusion.colorTrilinear_invariant,
    ``GUT.SU5.FortyElectronExclusion.colorTrilinear_unique,
    ``GUT.SU5.FortyElectronExclusion.basis_vanish,
    ``GUT.SU5.FortyElectronExclusion.raw_functional_alternating,
    ``GUT.SU5.FortyElectronExclusion.functional_projection_zero,
    ``GUT.SU5.FortyElectronExclusion.kernel_electron_zero,
    ``GUT.SU5.FortyElectronExclusion.electron_hom_zero,
    ``GUT.SU5.FortyElectronExclusion.electron_multiplicity_zero,
    ``GUT.SU5.FortyElectronExclusion.selected_multiplicity_result]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forty selected multiplicities: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Forty selected multiplicities: {ds.length} strict transitive checks passed"
