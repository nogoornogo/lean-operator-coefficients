import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureMixed
import Physics.FieldTheory.Jets.LorentzJetIBP
import Math.RepresentationTheory.LagrangianInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureMixed instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DerivativeLiteratureMixed.A => Physics.DerivativeLiteratureMixed.A,
  GUT.DerivativeLiteratureMixed.D => Physics.DerivativeLiteratureMixed.D,
  GUT.DerivativeLiteratureMixed.Label => Physics.DerivativeLiteratureMixed.Label,
  GUT.DerivativeLiteratureMixed.candidate => Physics.DerivativeLiteratureMixed.candidate,
  GUT.DerivativeLiteratureMixed.candidate_extraction => Physics.DerivativeLiteratureMixed.candidate_extraction,
  GUT.DerivativeLiteratureMixed.current => Physics.DerivativeLiteratureMixed.current,
  GUT.DerivativeLiteratureMixed.current.eq_1 => Physics.DerivativeLiteratureMixed.current.eq_1,
  GUT.DerivativeLiteratureMixed.current_ibp => Physics.DerivativeLiteratureMixed.current_ibp,
  GUT.DerivativeLiteratureMixed.current_reorder => Physics.DerivativeLiteratureMixed.current_reorder,
  GUT.DerivativeLiteratureMixed.divergence => Physics.DerivativeLiteratureMixed.divergence,
  GUT.DerivativeLiteratureMixed.h => Physics.DerivativeLiteratureMixed.h,
  GUT.DerivativeLiteratureMixed.higgsCurrent => Physics.DerivativeLiteratureMixed.higgsCurrent,
  GUT.DerivativeLiteratureMixed.ibp => Physics.DerivativeLiteratureMixed.ibp,
  GUT.DerivativeLiteratureMixed.input => Physics.DerivativeLiteratureMixed.input,
  GUT.DerivativeLiteratureMixed.instAddCommGroupA => Physics.DerivativeLiteratureMixed.instAddCommGroupA,
  GUT.DerivativeLiteratureMixed.instModuleComplexA => Physics.DerivativeLiteratureMixed.instModuleComplexA,
  GUT.DerivativeLiteratureMixed.instRingA => Physics.DerivativeLiteratureMixed.instRingA,
  GUT.DerivativeLiteratureMixed.odd_swap => Physics.DerivativeLiteratureMixed.odd_swap,
  GUT.DerivativeLiteratureMixed.psi => Physics.DerivativeLiteratureMixed.psi,
  GUT.DerivativeLiteratureMixed.reversed => Physics.DerivativeLiteratureMixed.reversed,
  GUT.DerivativeLiteratureMixed.reversed.eq_1 => Physics.DerivativeLiteratureMixed.reversed.eq_1,
  GUT.DerivativeLiteratureMixed.rho => Physics.DerivativeLiteratureMixed.rho,
  GUT.DerivativeLiteratureMixed.sigma => Physics.DerivativeLiteratureMixed.sigma
]

assert_compatible GUT.DerivativeLiteratureMixed.A => Physics.DerivativeLiteratureMixed.A
assert_compatible GUT.DerivativeLiteratureMixed.D => Physics.DerivativeLiteratureMixed.D
assert_compatible GUT.DerivativeLiteratureMixed.Label => Physics.DerivativeLiteratureMixed.Label
assert_compatible GUT.DerivativeLiteratureMixed.candidate => Physics.DerivativeLiteratureMixed.candidate
assert_compatible GUT.DerivativeLiteratureMixed.candidate_extraction => Physics.DerivativeLiteratureMixed.candidate_extraction
assert_compatible GUT.DerivativeLiteratureMixed.current => Physics.DerivativeLiteratureMixed.current
assert_compatible GUT.DerivativeLiteratureMixed.current.eq_1 => Physics.DerivativeLiteratureMixed.current.eq_1
assert_compatible GUT.DerivativeLiteratureMixed.current_ibp => Physics.DerivativeLiteratureMixed.current_ibp
assert_compatible GUT.DerivativeLiteratureMixed.current_reorder => Physics.DerivativeLiteratureMixed.current_reorder
assert_compatible GUT.DerivativeLiteratureMixed.divergence => Physics.DerivativeLiteratureMixed.divergence
assert_compatible GUT.DerivativeLiteratureMixed.h => Physics.DerivativeLiteratureMixed.h
assert_compatible GUT.DerivativeLiteratureMixed.higgsCurrent => Physics.DerivativeLiteratureMixed.higgsCurrent
assert_compatible GUT.DerivativeLiteratureMixed.ibp => Physics.DerivativeLiteratureMixed.ibp
assert_compatible GUT.DerivativeLiteratureMixed.input => Physics.DerivativeLiteratureMixed.input
assert_compatible GUT.DerivativeLiteratureMixed.instAddCommGroupA => Physics.DerivativeLiteratureMixed.instAddCommGroupA
assert_compatible GUT.DerivativeLiteratureMixed.instModuleComplexA => Physics.DerivativeLiteratureMixed.instModuleComplexA
assert_compatible GUT.DerivativeLiteratureMixed.instRingA => Physics.DerivativeLiteratureMixed.instRingA
assert_compatible GUT.DerivativeLiteratureMixed.odd_swap => Physics.DerivativeLiteratureMixed.odd_swap
assert_compatible GUT.DerivativeLiteratureMixed.psi => Physics.DerivativeLiteratureMixed.psi
assert_compatible GUT.DerivativeLiteratureMixed.reversed => Physics.DerivativeLiteratureMixed.reversed
assert_compatible GUT.DerivativeLiteratureMixed.reversed.eq_1 => Physics.DerivativeLiteratureMixed.reversed.eq_1
assert_compatible GUT.DerivativeLiteratureMixed.rho => Physics.DerivativeLiteratureMixed.rho
assert_compatible GUT.DerivativeLiteratureMixed.sigma => Physics.DerivativeLiteratureMixed.sigma
