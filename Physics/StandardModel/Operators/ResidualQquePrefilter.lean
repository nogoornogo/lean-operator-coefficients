import Physics.StandardModel.Operators.BaryonOne.Qque.ResidualQquePrefilter
import Physics.StandardModel.Operators.NeutralQqueExterior
import Math.RepresentationTheory.ProtectionConstraintPullback
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.ResidualQquePrefilter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ResidualQquePrefilter.Forbids => Physics.ResidualQquePrefilter.Forbids,
  GUT.ResidualQquePrefilter.Necessary => Physics.ResidualQquePrefilter.Necessary,
  GUT.ResidualQquePrefilter.Triplet => Physics.ResidualQquePrefilter.Triplet,
  GUT.ResidualQquePrefilter.Triplet.EC => Physics.ResidualQquePrefilter.Triplet.EC,
  GUT.ResidualQquePrefilter.Triplet.HasCoefficient => Physics.ResidualQquePrefilter.Triplet.HasCoefficient,
  GUT.ResidualQquePrefilter.Triplet.Q => Physics.ResidualQquePrefilter.Triplet.Q,
  GUT.ResidualQquePrefilter.Triplet.UC => Physics.ResidualQquePrefilter.Triplet.UC,
  GUT.ResidualQquePrefilter.Triplet.casesOn => Physics.ResidualQquePrefilter.Triplet.casesOn,
  GUT.ResidualQquePrefilter.Triplet.charges => Physics.ResidualQquePrefilter.Triplet.charges,
  GUT.ResidualQquePrefilter.Triplet.ctorIdx => Physics.ResidualQquePrefilter.Triplet.ctorIdx,
  GUT.ResidualQquePrefilter.Triplet.eEquiv => Physics.ResidualQquePrefilter.Triplet.eEquiv,
  GUT.ResidualQquePrefilter.Triplet.mk => Physics.ResidualQquePrefilter.Triplet.mk,
  GUT.ResidualQquePrefilter.Triplet.mk.inj => Physics.ResidualQquePrefilter.Triplet.mk.inj,
  GUT.ResidualQquePrefilter.Triplet.mk.injEq => Physics.ResidualQquePrefilter.Triplet.mk.injEq,
  GUT.ResidualQquePrefilter.Triplet.mk.noConfusion => Physics.ResidualQquePrefilter.Triplet.mk.noConfusion,
  GUT.ResidualQquePrefilter.Triplet.mk.sizeOf_spec => Physics.ResidualQquePrefilter.Triplet.mk.sizeOf_spec,
  GUT.ResidualQquePrefilter.Triplet.neutral_hasCoefficient => Physics.ResidualQquePrefilter.Triplet.neutral_hasCoefficient,
  GUT.ResidualQquePrefilter.Triplet.noConfusion => Physics.ResidualQquePrefilter.Triplet.noConfusion,
  GUT.ResidualQquePrefilter.Triplet.noConfusionType => Physics.ResidualQquePrefilter.Triplet.noConfusionType,
  GUT.ResidualQquePrefilter.Triplet.qEquiv => Physics.ResidualQquePrefilter.Triplet.qEquiv,
  GUT.ResidualQquePrefilter.Triplet.rec => Physics.ResidualQquePrefilter.Triplet.rec,
  GUT.ResidualQquePrefilter.Triplet.recOn => Physics.ResidualQquePrefilter.Triplet.recOn,
  GUT.ResidualQquePrefilter.Triplet.rightElectronEquiv => Physics.ResidualQquePrefilter.Triplet.rightElectronEquiv,
  GUT.ResidualQquePrefilter.Triplet.rightUpEquiv => Physics.ResidualQquePrefilter.Triplet.rightUpEquiv,
  GUT.ResidualQquePrefilter.Triplet.uEquiv => Physics.ResidualQquePrefilter.Triplet.uEquiv,
  GUT.ResidualQquePrefilter.block_excludes => Physics.ResidualQquePrefilter.block_excludes,
  GUT.ResidualQquePrefilter.chargedMap => Physics.ResidualQquePrefilter.chargedMap,
  GUT.ResidualQquePrefilter.equal_species_excludes => Physics.ResidualQquePrefilter.equal_species_excludes,
  GUT.ResidualQquePrefilter.finiteCandidates => Physics.ResidualQquePrefilter.finiteCandidates,
  GUT.ResidualQquePrefilter.finite_preserve => Physics.ResidualQquePrefilter.finite_preserve,
  GUT.ResidualQquePrefilter.instAddCommGroupQuark => Physics.ResidualQquePrefilter.instAddCommGroupQuark,
  GUT.ResidualQquePrefilter.necessary => Physics.ResidualQquePrefilter.necessary,
  GUT.ResidualQquePrefilter.neutral_excludes => Physics.ResidualQquePrefilter.neutral_excludes,
  GUT.ResidualQquePrefilter.preserve => Physics.ResidualQquePrefilter.preserve,
  GUT.ResidualQquePrefilter.reject => Physics.ResidualQquePrefilter.reject,
  GUT.ResidualQquePrefilter.retain => Physics.ResidualQquePrefilter.retain,
  GUT.ResidualQquePrefilter.selectedAction => Physics.ResidualQquePrefilter.selectedAction,
  GUT.ResidualQquePrefilter.selectedRetain => Physics.ResidualQquePrefilter.selectedRetain,
  GUT.ResidualQquePrefilter.selectedTriplet => Physics.ResidualQquePrefilter.selectedTriplet,
  GUT.ResidualQquePrefilter.selected_neutral_reject => Physics.ResidualQquePrefilter.selected_neutral_reject,
  GUT.ResidualQquePrefilter.selected_preserve => Physics.ResidualQquePrefilter.selected_preserve
]

assert_compatible GUT.ResidualQquePrefilter.Forbids => Physics.ResidualQquePrefilter.Forbids
assert_compatible GUT.ResidualQquePrefilter.Necessary => Physics.ResidualQquePrefilter.Necessary
assert_compatible GUT.ResidualQquePrefilter.Triplet => Physics.ResidualQquePrefilter.Triplet
assert_compatible GUT.ResidualQquePrefilter.Triplet.EC => Physics.ResidualQquePrefilter.Triplet.EC
assert_compatible GUT.ResidualQquePrefilter.Triplet.HasCoefficient => Physics.ResidualQquePrefilter.Triplet.HasCoefficient
assert_compatible GUT.ResidualQquePrefilter.Triplet.Q => Physics.ResidualQquePrefilter.Triplet.Q
assert_compatible GUT.ResidualQquePrefilter.Triplet.UC => Physics.ResidualQquePrefilter.Triplet.UC
assert_compatible GUT.ResidualQquePrefilter.Triplet.casesOn => Physics.ResidualQquePrefilter.Triplet.casesOn
assert_compatible GUT.ResidualQquePrefilter.Triplet.charges => Physics.ResidualQquePrefilter.Triplet.charges
assert_compatible GUT.ResidualQquePrefilter.Triplet.ctorIdx => Physics.ResidualQquePrefilter.Triplet.ctorIdx
assert_compatible GUT.ResidualQquePrefilter.Triplet.eEquiv => Physics.ResidualQquePrefilter.Triplet.eEquiv
assert_compatible GUT.ResidualQquePrefilter.Triplet.mk => Physics.ResidualQquePrefilter.Triplet.mk
assert_compatible GUT.ResidualQquePrefilter.Triplet.mk.inj => Physics.ResidualQquePrefilter.Triplet.mk.inj
assert_compatible GUT.ResidualQquePrefilter.Triplet.mk.injEq => Physics.ResidualQquePrefilter.Triplet.mk.injEq
assert_compatible GUT.ResidualQquePrefilter.Triplet.mk.noConfusion => Physics.ResidualQquePrefilter.Triplet.mk.noConfusion
assert_compatible GUT.ResidualQquePrefilter.Triplet.mk.sizeOf_spec => Physics.ResidualQquePrefilter.Triplet.mk.sizeOf_spec
assert_compatible GUT.ResidualQquePrefilter.Triplet.neutral_hasCoefficient => Physics.ResidualQquePrefilter.Triplet.neutral_hasCoefficient
assert_compatible GUT.ResidualQquePrefilter.Triplet.noConfusion => Physics.ResidualQquePrefilter.Triplet.noConfusion
assert_compatible GUT.ResidualQquePrefilter.Triplet.noConfusionType => Physics.ResidualQquePrefilter.Triplet.noConfusionType
assert_compatible GUT.ResidualQquePrefilter.Triplet.qEquiv => Physics.ResidualQquePrefilter.Triplet.qEquiv
assert_compatible GUT.ResidualQquePrefilter.Triplet.rec => Physics.ResidualQquePrefilter.Triplet.rec
assert_compatible GUT.ResidualQquePrefilter.Triplet.recOn => Physics.ResidualQquePrefilter.Triplet.recOn
assert_compatible GUT.ResidualQquePrefilter.Triplet.rightElectronEquiv => Physics.ResidualQquePrefilter.Triplet.rightElectronEquiv
assert_compatible GUT.ResidualQquePrefilter.Triplet.rightUpEquiv => Physics.ResidualQquePrefilter.Triplet.rightUpEquiv
assert_compatible GUT.ResidualQquePrefilter.Triplet.uEquiv => Physics.ResidualQquePrefilter.Triplet.uEquiv
assert_compatible GUT.ResidualQquePrefilter.block_excludes => Physics.ResidualQquePrefilter.block_excludes
assert_compatible GUT.ResidualQquePrefilter.chargedMap => Physics.ResidualQquePrefilter.chargedMap
assert_compatible GUT.ResidualQquePrefilter.equal_species_excludes => Physics.ResidualQquePrefilter.equal_species_excludes
assert_compatible GUT.ResidualQquePrefilter.finiteCandidates => Physics.ResidualQquePrefilter.finiteCandidates
assert_compatible GUT.ResidualQquePrefilter.finite_preserve => Physics.ResidualQquePrefilter.finite_preserve
assert_compatible GUT.ResidualQquePrefilter.instAddCommGroupQuark => Physics.ResidualQquePrefilter.instAddCommGroupQuark
assert_compatible GUT.ResidualQquePrefilter.necessary => Physics.ResidualQquePrefilter.necessary
assert_compatible GUT.ResidualQquePrefilter.neutral_excludes => Physics.ResidualQquePrefilter.neutral_excludes
assert_compatible GUT.ResidualQquePrefilter.preserve => Physics.ResidualQquePrefilter.preserve
assert_compatible GUT.ResidualQquePrefilter.reject => Physics.ResidualQquePrefilter.reject
assert_compatible GUT.ResidualQquePrefilter.retain => Physics.ResidualQquePrefilter.retain
assert_compatible GUT.ResidualQquePrefilter.selectedAction => Physics.ResidualQquePrefilter.selectedAction
assert_compatible GUT.ResidualQquePrefilter.selectedRetain => Physics.ResidualQquePrefilter.selectedRetain
assert_compatible GUT.ResidualQquePrefilter.selectedTriplet => Physics.ResidualQquePrefilter.selectedTriplet
assert_compatible GUT.ResidualQquePrefilter.selected_neutral_reject => Physics.ResidualQquePrefilter.selected_neutral_reject
assert_compatible GUT.ResidualQquePrefilter.selected_preserve => Physics.ResidualQquePrefilter.selected_preserve
