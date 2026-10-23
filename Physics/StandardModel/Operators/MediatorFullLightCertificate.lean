import Physics.StandardModel.Operators.Selection.MediatorFullLightCertificate
import Physics.StandardModel.Operators.FullLightSpeciesQque
import Physics.StandardModel.Operators.MediatorQqueEvaluation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.MediatorFullLightCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MediatorFullLightCertificate.Certificate => Physics.MediatorFullLightCertificate.Certificate,
  GUT.MediatorFullLightCertificate.Certificate.a => Physics.MediatorFullLightCertificate.Certificate.a,
  GUT.MediatorFullLightCertificate.Certificate.b => Physics.MediatorFullLightCertificate.Certificate.b,
  GUT.MediatorFullLightCertificate.Certificate.casesOn => Physics.MediatorFullLightCertificate.Certificate.casesOn,
  GUT.MediatorFullLightCertificate.Certificate.ctorIdx => Physics.MediatorFullLightCertificate.Certificate.ctorIdx,
  GUT.MediatorFullLightCertificate.Certificate.generated => Physics.MediatorFullLightCertificate.Certificate.generated,
  GUT.MediatorFullLightCertificate.Certificate.generated_nonzero => Physics.MediatorFullLightCertificate.Certificate.generated_nonzero,
  GUT.MediatorFullLightCertificate.Certificate.hasCoefficient => Physics.MediatorFullLightCertificate.Certificate.hasCoefficient,
  GUT.MediatorFullLightCertificate.Certificate.hasResidualMap => Physics.MediatorFullLightCertificate.Certificate.hasResidualMap,
  GUT.MediatorFullLightCertificate.Certificate.invariant => Physics.MediatorFullLightCertificate.Certificate.invariant,
  GUT.MediatorFullLightCertificate.Certificate.l => Physics.MediatorFullLightCertificate.Certificate.l,
  GUT.MediatorFullLightCertificate.Certificate.mk => Physics.MediatorFullLightCertificate.Certificate.mk,
  GUT.MediatorFullLightCertificate.Certificate.mk.inj => Physics.MediatorFullLightCertificate.Certificate.mk.inj,
  GUT.MediatorFullLightCertificate.Certificate.mk.injEq => Physics.MediatorFullLightCertificate.Certificate.mk.injEq,
  GUT.MediatorFullLightCertificate.Certificate.mk.noConfusion => Physics.MediatorFullLightCertificate.Certificate.mk.noConfusion,
  GUT.MediatorFullLightCertificate.Certificate.mk.sizeOf_spec => Physics.MediatorFullLightCertificate.Certificate.mk.sizeOf_spec,
  GUT.MediatorFullLightCertificate.Certificate.noConfusion => Physics.MediatorFullLightCertificate.Certificate.noConfusion,
  GUT.MediatorFullLightCertificate.Certificate.noConfusionType => Physics.MediatorFullLightCertificate.Certificate.noConfusionType,
  GUT.MediatorFullLightCertificate.Certificate.probe => Physics.MediatorFullLightCertificate.Certificate.probe,
  GUT.MediatorFullLightCertificate.Certificate.rec => Physics.MediatorFullLightCertificate.Certificate.rec,
  GUT.MediatorFullLightCertificate.Certificate.recOn => Physics.MediatorFullLightCertificate.Certificate.recOn,
  GUT.MediatorFullLightCertificate.Certificate.reconstruct => Physics.MediatorFullLightCertificate.Certificate.reconstruct,
  GUT.MediatorFullLightCertificate.Certificate.residualHom => Physics.MediatorFullLightCertificate.Certificate.residualHom,
  GUT.MediatorFullLightCertificate.Certificate.residualHom_nonzero => Physics.MediatorFullLightCertificate.Certificate.residualHom_nonzero,
  GUT.MediatorFullLightCertificate.Certificate.s => Physics.MediatorFullLightCertificate.Certificate.s,
  GUT.MediatorFullLightCertificate.Certificate.t => Physics.MediatorFullLightCertificate.Certificate.t,
  GUT.MediatorFullLightCertificate.Certificate.x => Physics.MediatorFullLightCertificate.Certificate.x,
  GUT.MediatorFullLightCertificate.Certificate.y => Physics.MediatorFullLightCertificate.Certificate.y,
  GUT.MediatorFullLightCertificate.Certificate.z => Physics.MediatorFullLightCertificate.Certificate.z,
  GUT.MediatorFullLightCertificate.E => Physics.MediatorFullLightCertificate.E,
  GUT.MediatorFullLightCertificate.Q => Physics.MediatorFullLightCertificate.Q,
  GUT.MediatorFullLightCertificate.U => Physics.MediatorFullLightCertificate.U,
  GUT.MediatorFullLightCertificate.eRep => Physics.MediatorFullLightCertificate.eRep,
  GUT.MediatorFullLightCertificate.ofRestriction => Physics.MediatorFullLightCertificate.ofRestriction,
  GUT.MediatorFullLightCertificate.qRep => Physics.MediatorFullLightCertificate.qRep,
  GUT.MediatorFullLightCertificate.uRep => Physics.MediatorFullLightCertificate.uRep
]

assert_compatible GUT.MediatorFullLightCertificate.Certificate => Physics.MediatorFullLightCertificate.Certificate
assert_compatible GUT.MediatorFullLightCertificate.Certificate.a => Physics.MediatorFullLightCertificate.Certificate.a
assert_compatible GUT.MediatorFullLightCertificate.Certificate.b => Physics.MediatorFullLightCertificate.Certificate.b
assert_compatible GUT.MediatorFullLightCertificate.Certificate.casesOn => Physics.MediatorFullLightCertificate.Certificate.casesOn
assert_compatible GUT.MediatorFullLightCertificate.Certificate.ctorIdx => Physics.MediatorFullLightCertificate.Certificate.ctorIdx
assert_compatible GUT.MediatorFullLightCertificate.Certificate.generated => Physics.MediatorFullLightCertificate.Certificate.generated
assert_compatible GUT.MediatorFullLightCertificate.Certificate.generated_nonzero => Physics.MediatorFullLightCertificate.Certificate.generated_nonzero
assert_compatible GUT.MediatorFullLightCertificate.Certificate.hasCoefficient => Physics.MediatorFullLightCertificate.Certificate.hasCoefficient
assert_compatible GUT.MediatorFullLightCertificate.Certificate.hasResidualMap => Physics.MediatorFullLightCertificate.Certificate.hasResidualMap
assert_compatible GUT.MediatorFullLightCertificate.Certificate.invariant => Physics.MediatorFullLightCertificate.Certificate.invariant
assert_compatible GUT.MediatorFullLightCertificate.Certificate.l => Physics.MediatorFullLightCertificate.Certificate.l
assert_compatible GUT.MediatorFullLightCertificate.Certificate.mk => Physics.MediatorFullLightCertificate.Certificate.mk
assert_compatible GUT.MediatorFullLightCertificate.Certificate.mk.inj => Physics.MediatorFullLightCertificate.Certificate.mk.inj
assert_compatible GUT.MediatorFullLightCertificate.Certificate.mk.injEq => Physics.MediatorFullLightCertificate.Certificate.mk.injEq
assert_compatible GUT.MediatorFullLightCertificate.Certificate.mk.noConfusion => Physics.MediatorFullLightCertificate.Certificate.mk.noConfusion
assert_compatible GUT.MediatorFullLightCertificate.Certificate.mk.sizeOf_spec => Physics.MediatorFullLightCertificate.Certificate.mk.sizeOf_spec
assert_compatible GUT.MediatorFullLightCertificate.Certificate.noConfusion => Physics.MediatorFullLightCertificate.Certificate.noConfusion
assert_compatible GUT.MediatorFullLightCertificate.Certificate.noConfusionType => Physics.MediatorFullLightCertificate.Certificate.noConfusionType
assert_compatible GUT.MediatorFullLightCertificate.Certificate.probe => Physics.MediatorFullLightCertificate.Certificate.probe
assert_compatible GUT.MediatorFullLightCertificate.Certificate.rec => Physics.MediatorFullLightCertificate.Certificate.rec
assert_compatible GUT.MediatorFullLightCertificate.Certificate.recOn => Physics.MediatorFullLightCertificate.Certificate.recOn
assert_compatible GUT.MediatorFullLightCertificate.Certificate.reconstruct => Physics.MediatorFullLightCertificate.Certificate.reconstruct
assert_compatible GUT.MediatorFullLightCertificate.Certificate.residualHom => Physics.MediatorFullLightCertificate.Certificate.residualHom
assert_compatible GUT.MediatorFullLightCertificate.Certificate.residualHom_nonzero => Physics.MediatorFullLightCertificate.Certificate.residualHom_nonzero
assert_compatible GUT.MediatorFullLightCertificate.Certificate.s => Physics.MediatorFullLightCertificate.Certificate.s
assert_compatible GUT.MediatorFullLightCertificate.Certificate.t => Physics.MediatorFullLightCertificate.Certificate.t
assert_compatible GUT.MediatorFullLightCertificate.Certificate.x => Physics.MediatorFullLightCertificate.Certificate.x
assert_compatible GUT.MediatorFullLightCertificate.Certificate.y => Physics.MediatorFullLightCertificate.Certificate.y
assert_compatible GUT.MediatorFullLightCertificate.Certificate.z => Physics.MediatorFullLightCertificate.Certificate.z
assert_compatible GUT.MediatorFullLightCertificate.E => Physics.MediatorFullLightCertificate.E
assert_compatible GUT.MediatorFullLightCertificate.Q => Physics.MediatorFullLightCertificate.Q
assert_compatible GUT.MediatorFullLightCertificate.U => Physics.MediatorFullLightCertificate.U
assert_compatible GUT.MediatorFullLightCertificate.eRep => Physics.MediatorFullLightCertificate.eRep
assert_compatible GUT.MediatorFullLightCertificate.ofRestriction => Physics.MediatorFullLightCertificate.ofRestriction
assert_compatible GUT.MediatorFullLightCertificate.qRep => Physics.MediatorFullLightCertificate.qRep
assert_compatible GUT.MediatorFullLightCertificate.uRep => Physics.MediatorFullLightCertificate.uRep
