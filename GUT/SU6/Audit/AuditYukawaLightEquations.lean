import GUT.SU6.Yukawa.LightEquations
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6YukawaLight.contract_basis,
    ``GUT.SU6YukawaLight.contract_last, ``GUT.SU6YukawaLight.dual_single,
    ``GUT.SU6YukawaLight.row_exterior, ``GUT.SU6YukawaLight.row_first,
    ``GUT.SU6YukawaLight.row_second, ``GUT.SU6YukawaLight.vanishes_iff,
    ``GUT.SU6YukawaLight.radical_iff, ``GUT.SU6YukawaLight.constraints,
    ``GUT.SU6YukawaLight.constraints_apply, ``GUT.SU6YukawaLight.constraints_ker,
    ``GUT.SU6YukawaLight.radical_eq_kernel, ``GUT.SU6YukawaLight.radicalKernelEquiv,
    ``GUT.SU6YukawaLight.generatedMass, ``GUT.SU6YukawaLight.generatedMass_form,
    ``GUT.SU6YukawaLight.all_yukawas, ``GUT.SU6YukawaLight.untouched_light,
    ``GUT.SU6YukawaLight.pureSinglet_conditions, ``GUT.SU6YukawaLight.pureSinglet_light_iff,
    ``GUT.SU6YukawaLight.nonzero_couplings_light_singlet]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU6 Yukawa light equations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU6 Yukawa light equations: {declarations.length} strict axiom checks passed"
