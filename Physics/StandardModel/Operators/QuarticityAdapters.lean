import Physics.StandardModel.Operators.Selection.QuarticityAdapters
import Physics.StandardModel.Operators.ComposableBLSupport
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.CyclicCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.QuarticityAdapters instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QuarticityAdapters.Bare => Physics.QuarticityAdapters.Bare,
  GUT.QuarticityAdapters.Dressed => Physics.QuarticityAdapters.Dressed,
  GUT.QuarticityAdapters.H => Physics.QuarticityAdapters.H,
  GUT.QuarticityAdapters.P => Physics.QuarticityAdapters.P,
  GUT.QuarticityAdapters.bare_forbidden => Physics.QuarticityAdapters.bare_forbidden,
  GUT.QuarticityAdapters.blCharacter => Physics.QuarticityAdapters.blCharacter,
  GUT.QuarticityAdapters.blCharacter.eq_1 => Physics.QuarticityAdapters.blCharacter.eq_1,
  GUT.QuarticityAdapters.chi => Physics.QuarticityAdapters.chi,
  GUT.QuarticityAdapters.chi.eq_1 => Physics.QuarticityAdapters.chi.eq_1,
  GUT.QuarticityAdapters.chi_mul => Physics.QuarticityAdapters.chi_mul,
  GUT.QuarticityAdapters.compensated => Physics.QuarticityAdapters.compensated,
  GUT.QuarticityAdapters.copies => Physics.QuarticityAdapters.copies,
  GUT.QuarticityAdapters.copies.eq_1 => Physics.QuarticityAdapters.copies.eq_1,
  GUT.QuarticityAdapters.detector => Physics.QuarticityAdapters.detector,
  GUT.QuarticityAdapters.detector_square => Physics.QuarticityAdapters.detector_square,
  GUT.QuarticityAdapters.dressed => Physics.QuarticityAdapters.dressed,
  GUT.QuarticityAdapters.dressed_evaluation => Physics.QuarticityAdapters.dressed_evaluation,
  GUT.QuarticityAdapters.dressed_nonzero => Physics.QuarticityAdapters.dressed_nonzero,
  GUT.QuarticityAdapters.epsilonExterior => Physics.QuarticityAdapters.epsilonExterior,
  GUT.QuarticityAdapters.epsilonExterior.eq_1 => Physics.QuarticityAdapters.epsilonExterior.eq_1,
  GUT.QuarticityAdapters.epsilonExterior_apply => Physics.QuarticityAdapters.epsilonExterior_apply,
  GUT.QuarticityAdapters.epsilon_neutrino => Physics.QuarticityAdapters.epsilon_neutrino,
  GUT.QuarticityAdapters.eta => Physics.QuarticityAdapters.eta,
  GUT.QuarticityAdapters.eta.eq_1 => Physics.QuarticityAdapters.eta.eq_1,
  GUT.QuarticityAdapters.eta_action => Physics.QuarticityAdapters.eta_action,
  GUT.QuarticityAdapters.eta_gauge_neutral => Physics.QuarticityAdapters.eta_gauge_neutral,
  GUT.QuarticityAdapters.eta_phase_real => Physics.QuarticityAdapters.eta_phase_real,
  GUT.QuarticityAdapters.eta_phase_square => Physics.QuarticityAdapters.eta_phase_square,
  GUT.QuarticityAdapters.exists_dressed => Physics.QuarticityAdapters.exists_dressed,
  GUT.QuarticityAdapters.instAddCommGroupSubtypeExteriorAlgebraComplexSpaceMemSubmoduleExteriorPowerOfNatNat => Physics.QuarticityAdapters.instAddCommGroupSubtypeExteriorAlgebraComplexSpaceMemSubmoduleExteriorPowerOfNatNat,
  GUT.QuarticityAdapters.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraSpaceMemSubmoduleExteriorPowerOfNatNat => Physics.QuarticityAdapters.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraSpaceMemSubmoduleExteriorPowerOfNatNat,
  GUT.QuarticityAdapters.lTwo_detect => Physics.QuarticityAdapters.lTwo_detect,
  GUT.QuarticityAdapters.neutrino => Physics.QuarticityAdapters.neutrino,
  GUT.QuarticityAdapters.neutrino.eq_1 => Physics.QuarticityAdapters.neutrino.eq_1,
  GUT.QuarticityAdapters.neutrino_action => Physics.QuarticityAdapters.neutrino_action,
  GUT.QuarticityAdapters.neutrino_gauge_neutral => Physics.QuarticityAdapters.neutrino_gauge_neutral,
  GUT.QuarticityAdapters.smFlavor => Physics.QuarticityAdapters.smFlavor,
  GUT.QuarticityAdapters.smScalar => Physics.QuarticityAdapters.smScalar,
  GUT.QuarticityAdapters.sm_lTwo_forbidden => Physics.QuarticityAdapters.sm_lTwo_forbidden
]

assert_compatible GUT.QuarticityAdapters.Bare => Physics.QuarticityAdapters.Bare
assert_compatible GUT.QuarticityAdapters.Dressed => Physics.QuarticityAdapters.Dressed
assert_compatible GUT.QuarticityAdapters.H => Physics.QuarticityAdapters.H
assert_compatible GUT.QuarticityAdapters.P => Physics.QuarticityAdapters.P
assert_compatible GUT.QuarticityAdapters.bare_forbidden => Physics.QuarticityAdapters.bare_forbidden
assert_compatible GUT.QuarticityAdapters.blCharacter => Physics.QuarticityAdapters.blCharacter
assert_compatible GUT.QuarticityAdapters.blCharacter.eq_1 => Physics.QuarticityAdapters.blCharacter.eq_1
assert_compatible GUT.QuarticityAdapters.chi => Physics.QuarticityAdapters.chi
assert_compatible GUT.QuarticityAdapters.chi.eq_1 => Physics.QuarticityAdapters.chi.eq_1
assert_compatible GUT.QuarticityAdapters.chi_mul => Physics.QuarticityAdapters.chi_mul
assert_compatible GUT.QuarticityAdapters.compensated => Physics.QuarticityAdapters.compensated
assert_compatible GUT.QuarticityAdapters.copies => Physics.QuarticityAdapters.copies
assert_compatible GUT.QuarticityAdapters.copies.eq_1 => Physics.QuarticityAdapters.copies.eq_1
assert_compatible GUT.QuarticityAdapters.detector => Physics.QuarticityAdapters.detector
assert_compatible GUT.QuarticityAdapters.detector_square => Physics.QuarticityAdapters.detector_square
assert_compatible GUT.QuarticityAdapters.dressed => Physics.QuarticityAdapters.dressed
assert_compatible GUT.QuarticityAdapters.dressed_evaluation => Physics.QuarticityAdapters.dressed_evaluation
assert_compatible GUT.QuarticityAdapters.dressed_nonzero => Physics.QuarticityAdapters.dressed_nonzero
assert_compatible GUT.QuarticityAdapters.epsilonExterior => Physics.QuarticityAdapters.epsilonExterior
assert_compatible GUT.QuarticityAdapters.epsilonExterior.eq_1 => Physics.QuarticityAdapters.epsilonExterior.eq_1
assert_compatible GUT.QuarticityAdapters.epsilonExterior_apply => Physics.QuarticityAdapters.epsilonExterior_apply
assert_compatible GUT.QuarticityAdapters.epsilon_neutrino => Physics.QuarticityAdapters.epsilon_neutrino
assert_compatible GUT.QuarticityAdapters.eta => Physics.QuarticityAdapters.eta
assert_compatible GUT.QuarticityAdapters.eta.eq_1 => Physics.QuarticityAdapters.eta.eq_1
assert_compatible GUT.QuarticityAdapters.eta_action => Physics.QuarticityAdapters.eta_action
assert_compatible GUT.QuarticityAdapters.eta_gauge_neutral => Physics.QuarticityAdapters.eta_gauge_neutral
assert_compatible GUT.QuarticityAdapters.eta_phase_real => Physics.QuarticityAdapters.eta_phase_real
assert_compatible GUT.QuarticityAdapters.eta_phase_square => Physics.QuarticityAdapters.eta_phase_square
assert_compatible GUT.QuarticityAdapters.exists_dressed => Physics.QuarticityAdapters.exists_dressed
assert_compatible GUT.QuarticityAdapters.instAddCommGroupSubtypeExteriorAlgebraComplexSpaceMemSubmoduleExteriorPowerOfNatNat => Physics.QuarticityAdapters.instAddCommGroupSubtypeExteriorAlgebraComplexSpaceMemSubmoduleExteriorPowerOfNatNat
assert_compatible GUT.QuarticityAdapters.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraSpaceMemSubmoduleExteriorPowerOfNatNat => Physics.QuarticityAdapters.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraSpaceMemSubmoduleExteriorPowerOfNatNat
assert_compatible GUT.QuarticityAdapters.lTwo_detect => Physics.QuarticityAdapters.lTwo_detect
assert_compatible GUT.QuarticityAdapters.neutrino => Physics.QuarticityAdapters.neutrino
assert_compatible GUT.QuarticityAdapters.neutrino.eq_1 => Physics.QuarticityAdapters.neutrino.eq_1
assert_compatible GUT.QuarticityAdapters.neutrino_action => Physics.QuarticityAdapters.neutrino_action
assert_compatible GUT.QuarticityAdapters.neutrino_gauge_neutral => Physics.QuarticityAdapters.neutrino_gauge_neutral
assert_compatible GUT.QuarticityAdapters.smFlavor => Physics.QuarticityAdapters.smFlavor
assert_compatible GUT.QuarticityAdapters.smScalar => Physics.QuarticityAdapters.smScalar
assert_compatible GUT.QuarticityAdapters.sm_lTwo_forbidden => Physics.QuarticityAdapters.sm_lTwo_forbidden
