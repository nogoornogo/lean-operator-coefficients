import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenModelInterface
import Physics.StandardModel.Operators.BnvSevenCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenModelInterface instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenModelInterface.bounded => Physics.BnvSevenModelInterface.bounded,
  GUT.BnvSevenModelInterface.boundedEquiv => Physics.BnvSevenModelInterface.boundedEquiv,
  GUT.BnvSevenModelInterface.coefficientEquiv => Physics.BnvSevenModelInterface.coefficientEquiv,
  GUT.BnvSevenModelInterface.forbidden_iff => Physics.BnvSevenModelInterface.forbidden_iff,
  GUT.BnvSevenModelInterface.mixedEquiv => Physics.BnvSevenModelInterface.mixedEquiv,
  GUT.BnvSevenModelInterface.piEquiv => Physics.BnvSevenModelInterface.piEquiv,
  GUT.BnvSevenModelInterface.pi_single => Physics.BnvSevenModelInterface.pi_single,
  GUT.BnvSevenModelInterface.pull => Physics.BnvSevenModelInterface.pull,
  GUT.BnvSevenModelInterface.pull_mem => Physics.BnvSevenModelInterface.pull_mem,
  GUT.BnvSevenModelInterface.pull_symm => Physics.BnvSevenModelInterface.pull_symm,
  GUT.BnvSevenModelInterface.residualEquiv => Physics.BnvSevenModelInterface.residualEquiv,
  GUT.BnvSevenModelInterface.sector => Physics.BnvSevenModelInterface.sector,
  GUT.BnvSevenModelInterface.sectorEquiv => Physics.BnvSevenModelInterface.sectorEquiv
]

assert_compatible GUT.BnvSevenModelInterface.bounded => Physics.BnvSevenModelInterface.bounded
assert_compatible GUT.BnvSevenModelInterface.boundedEquiv => Physics.BnvSevenModelInterface.boundedEquiv
assert_compatible GUT.BnvSevenModelInterface.coefficientEquiv => Physics.BnvSevenModelInterface.coefficientEquiv
assert_compatible GUT.BnvSevenModelInterface.forbidden_iff => Physics.BnvSevenModelInterface.forbidden_iff
assert_compatible GUT.BnvSevenModelInterface.mixedEquiv => Physics.BnvSevenModelInterface.mixedEquiv
assert_compatible GUT.BnvSevenModelInterface.piEquiv => Physics.BnvSevenModelInterface.piEquiv
assert_compatible GUT.BnvSevenModelInterface.pi_single => Physics.BnvSevenModelInterface.pi_single
assert_compatible GUT.BnvSevenModelInterface.pull => Physics.BnvSevenModelInterface.pull
assert_compatible GUT.BnvSevenModelInterface.pull_mem => Physics.BnvSevenModelInterface.pull_mem
assert_compatible GUT.BnvSevenModelInterface.pull_symm => Physics.BnvSevenModelInterface.pull_symm
assert_compatible GUT.BnvSevenModelInterface.residualEquiv => Physics.BnvSevenModelInterface.residualEquiv
assert_compatible GUT.BnvSevenModelInterface.sector => Physics.BnvSevenModelInterface.sector
assert_compatible GUT.BnvSevenModelInterface.sectorEquiv => Physics.BnvSevenModelInterface.sectorEquiv
