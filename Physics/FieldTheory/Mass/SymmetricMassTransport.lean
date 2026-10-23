import Physics.FieldTheory.Mass.Algebra.SymmetricMassTransport
import Physics.FieldTheory.Mass.InvariantWeylMass
import Physics.FieldTheory.Mass.UnitaryVirtualRealization
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.SymmetricMassTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SymmetricMassTransport.TransportCertificate => Physics.SymmetricMassTransport.TransportCertificate,
  GUT.SymmetricMassTransport.TransportCertificate.casesOn => Physics.SymmetricMassTransport.TransportCertificate.casesOn,
  GUT.SymmetricMassTransport.TransportCertificate.ctorIdx => Physics.SymmetricMassTransport.TransportCertificate.ctorIdx,
  GUT.SymmetricMassTransport.TransportCertificate.mass => Physics.SymmetricMassTransport.TransportCertificate.mass,
  GUT.SymmetricMassTransport.TransportCertificate.mass_heq => Physics.SymmetricMassTransport.TransportCertificate.mass_heq,
  GUT.SymmetricMassTransport.TransportCertificate.mk => Physics.SymmetricMassTransport.TransportCertificate.mk,
  GUT.SymmetricMassTransport.TransportCertificate.mk.inj => Physics.SymmetricMassTransport.TransportCertificate.mk.inj,
  GUT.SymmetricMassTransport.TransportCertificate.mk.injEq => Physics.SymmetricMassTransport.TransportCertificate.mk.injEq,
  GUT.SymmetricMassTransport.TransportCertificate.mk.noConfusion => Physics.SymmetricMassTransport.TransportCertificate.mk.noConfusion,
  GUT.SymmetricMassTransport.TransportCertificate.mk.sizeOf_spec => Physics.SymmetricMassTransport.TransportCertificate.mk.sizeOf_spec,
  GUT.SymmetricMassTransport.TransportCertificate.noConfusion => Physics.SymmetricMassTransport.TransportCertificate.noConfusion,
  GUT.SymmetricMassTransport.TransportCertificate.noConfusionType => Physics.SymmetricMassTransport.TransportCertificate.noConfusionType,
  GUT.SymmetricMassTransport.TransportCertificate.nonzero_iff => Physics.SymmetricMassTransport.TransportCertificate.nonzero_iff,
  GUT.SymmetricMassTransport.TransportCertificate.radicalEquiv => Physics.SymmetricMassTransport.TransportCertificate.radicalEquiv,
  GUT.SymmetricMassTransport.TransportCertificate.radical_character => Physics.SymmetricMassTransport.TransportCertificate.radical_character,
  GUT.SymmetricMassTransport.TransportCertificate.radical_finrank => Physics.SymmetricMassTransport.TransportCertificate.radical_finrank,
  GUT.SymmetricMassTransport.TransportCertificate.rec => Physics.SymmetricMassTransport.TransportCertificate.rec,
  GUT.SymmetricMassTransport.TransportCertificate.recOn => Physics.SymmetricMassTransport.TransportCertificate.recOn,
  GUT.SymmetricMassTransport.certificate => Physics.SymmetricMassTransport.certificate,
  GUT.SymmetricMassTransport.form_nonzero => Physics.SymmetricMassTransport.form_nonzero,
  GUT.SymmetricMassTransport.radicalEquiv => Physics.SymmetricMassTransport.radicalEquiv,
  GUT.SymmetricMassTransport.radical_character => Physics.SymmetricMassTransport.radical_character,
  GUT.SymmetricMassTransport.radical_finrank => Physics.SymmetricMassTransport.radical_finrank,
  GUT.SymmetricMassTransport.transport => Physics.SymmetricMassTransport.transport,
  GUT.SymmetricMassTransport.transport_heq => Physics.SymmetricMassTransport.transport_heq
]

assert_compatible GUT.SymmetricMassTransport.TransportCertificate => Physics.SymmetricMassTransport.TransportCertificate
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.casesOn => Physics.SymmetricMassTransport.TransportCertificate.casesOn
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.ctorIdx => Physics.SymmetricMassTransport.TransportCertificate.ctorIdx
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mass => Physics.SymmetricMassTransport.TransportCertificate.mass
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mass_heq => Physics.SymmetricMassTransport.TransportCertificate.mass_heq
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mk => Physics.SymmetricMassTransport.TransportCertificate.mk
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mk.inj => Physics.SymmetricMassTransport.TransportCertificate.mk.inj
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mk.injEq => Physics.SymmetricMassTransport.TransportCertificate.mk.injEq
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mk.noConfusion => Physics.SymmetricMassTransport.TransportCertificate.mk.noConfusion
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.mk.sizeOf_spec => Physics.SymmetricMassTransport.TransportCertificate.mk.sizeOf_spec
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.noConfusion => Physics.SymmetricMassTransport.TransportCertificate.noConfusion
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.noConfusionType => Physics.SymmetricMassTransport.TransportCertificate.noConfusionType
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.nonzero_iff => Physics.SymmetricMassTransport.TransportCertificate.nonzero_iff
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.radicalEquiv => Physics.SymmetricMassTransport.TransportCertificate.radicalEquiv
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.radical_character => Physics.SymmetricMassTransport.TransportCertificate.radical_character
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.radical_finrank => Physics.SymmetricMassTransport.TransportCertificate.radical_finrank
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.rec => Physics.SymmetricMassTransport.TransportCertificate.rec
assert_compatible GUT.SymmetricMassTransport.TransportCertificate.recOn => Physics.SymmetricMassTransport.TransportCertificate.recOn
assert_compatible GUT.SymmetricMassTransport.certificate => Physics.SymmetricMassTransport.certificate
assert_compatible GUT.SymmetricMassTransport.form_nonzero => Physics.SymmetricMassTransport.form_nonzero
assert_compatible GUT.SymmetricMassTransport.radicalEquiv => Physics.SymmetricMassTransport.radicalEquiv
assert_compatible GUT.SymmetricMassTransport.radical_character => Physics.SymmetricMassTransport.radical_character
assert_compatible GUT.SymmetricMassTransport.radical_finrank => Physics.SymmetricMassTransport.radical_finrank
assert_compatible GUT.SymmetricMassTransport.transport => Physics.SymmetricMassTransport.transport
assert_compatible GUT.SymmetricMassTransport.transport_heq => Physics.SymmetricMassTransport.transport_heq
