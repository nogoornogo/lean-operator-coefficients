import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionWitnesses
import Physics.StandardModel.Operators.SMB1DimensionBounds
import Physics.StandardModel.Operators.SMB1DimensionProposals
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionWitnesses instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1DimensionWitnesses.Attains => Physics.SMB1DimensionWitnesses.Attains,
  GUT.SMB1DimensionWitnesses.n11_attains => Physics.SMB1DimensionWitnesses.n11_attains,
  GUT.SMB1DimensionWitnesses.n13_attains => Physics.SMB1DimensionWitnesses.n13_attains,
  GUT.SMB1DimensionWitnesses.n15_attains => Physics.SMB1DimensionWitnesses.n15_attains,
  GUT.SMB1DimensionWitnesses.n17_attains => Physics.SMB1DimensionWitnesses.n17_attains,
  GUT.SMB1DimensionWitnesses.n1_attains => Physics.SMB1DimensionWitnesses.n1_attains,
  GUT.SMB1DimensionWitnesses.n3_attains => Physics.SMB1DimensionWitnesses.n3_attains,
  GUT.SMB1DimensionWitnesses.n5_attains => Physics.SMB1DimensionWitnesses.n5_attains,
  GUT.SMB1DimensionWitnesses.n7_attains => Physics.SMB1DimensionWitnesses.n7_attains,
  GUT.SMB1DimensionWitnesses.n9_attains => Physics.SMB1DimensionWitnesses.n9_attains,
  GUT.SMB1DimensionWitnesses.p11_attains => Physics.SMB1DimensionWitnesses.p11_attains,
  GUT.SMB1DimensionWitnesses.p13_attains => Physics.SMB1DimensionWitnesses.p13_attains,
  GUT.SMB1DimensionWitnesses.p15_attains => Physics.SMB1DimensionWitnesses.p15_attains,
  GUT.SMB1DimensionWitnesses.p17_attains => Physics.SMB1DimensionWitnesses.p17_attains,
  GUT.SMB1DimensionWitnesses.p1_attains => Physics.SMB1DimensionWitnesses.p1_attains,
  GUT.SMB1DimensionWitnesses.p3_attains => Physics.SMB1DimensionWitnesses.p3_attains,
  GUT.SMB1DimensionWitnesses.p5_attains => Physics.SMB1DimensionWitnesses.p5_attains,
  GUT.SMB1DimensionWitnesses.p7_attains => Physics.SMB1DimensionWitnesses.p7_attains,
  GUT.SMB1DimensionWitnesses.p9_attains => Physics.SMB1DimensionWitnesses.p9_attains,
  GUT.SMB1DimensionWitnesses.upperGrade => Physics.SMB1DimensionWitnesses.upperGrade,
  GUT.SMB1DimensionWitnesses.upper_attains => Physics.SMB1DimensionWitnesses.upper_attains
]

assert_compatible GUT.SMB1DimensionWitnesses.Attains => Physics.SMB1DimensionWitnesses.Attains
assert_compatible GUT.SMB1DimensionWitnesses.n11_attains => Physics.SMB1DimensionWitnesses.n11_attains
assert_compatible GUT.SMB1DimensionWitnesses.n13_attains => Physics.SMB1DimensionWitnesses.n13_attains
assert_compatible GUT.SMB1DimensionWitnesses.n15_attains => Physics.SMB1DimensionWitnesses.n15_attains
assert_compatible GUT.SMB1DimensionWitnesses.n17_attains => Physics.SMB1DimensionWitnesses.n17_attains
assert_compatible GUT.SMB1DimensionWitnesses.n1_attains => Physics.SMB1DimensionWitnesses.n1_attains
assert_compatible GUT.SMB1DimensionWitnesses.n3_attains => Physics.SMB1DimensionWitnesses.n3_attains
assert_compatible GUT.SMB1DimensionWitnesses.n5_attains => Physics.SMB1DimensionWitnesses.n5_attains
assert_compatible GUT.SMB1DimensionWitnesses.n7_attains => Physics.SMB1DimensionWitnesses.n7_attains
assert_compatible GUT.SMB1DimensionWitnesses.n9_attains => Physics.SMB1DimensionWitnesses.n9_attains
assert_compatible GUT.SMB1DimensionWitnesses.p11_attains => Physics.SMB1DimensionWitnesses.p11_attains
assert_compatible GUT.SMB1DimensionWitnesses.p13_attains => Physics.SMB1DimensionWitnesses.p13_attains
assert_compatible GUT.SMB1DimensionWitnesses.p15_attains => Physics.SMB1DimensionWitnesses.p15_attains
assert_compatible GUT.SMB1DimensionWitnesses.p17_attains => Physics.SMB1DimensionWitnesses.p17_attains
assert_compatible GUT.SMB1DimensionWitnesses.p1_attains => Physics.SMB1DimensionWitnesses.p1_attains
assert_compatible GUT.SMB1DimensionWitnesses.p3_attains => Physics.SMB1DimensionWitnesses.p3_attains
assert_compatible GUT.SMB1DimensionWitnesses.p5_attains => Physics.SMB1DimensionWitnesses.p5_attains
assert_compatible GUT.SMB1DimensionWitnesses.p7_attains => Physics.SMB1DimensionWitnesses.p7_attains
assert_compatible GUT.SMB1DimensionWitnesses.p9_attains => Physics.SMB1DimensionWitnesses.p9_attains
assert_compatible GUT.SMB1DimensionWitnesses.upperGrade => Physics.SMB1DimensionWitnesses.upperGrade
assert_compatible GUT.SMB1DimensionWitnesses.upper_attains => Physics.SMB1DimensionWitnesses.upper_attains
