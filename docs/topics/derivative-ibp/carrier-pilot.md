# Q18 Carrier Pilot

Status: compatibility endpoint completed on `audit/derivative-ibp-physlib-435`,
merged into `proof/derivative-ibp` and reverified. The parent remains unmerged
into master.

The user authorized the proposed carrier and mass-construction workarounds.
Start with Q18. Preserve `SMQ18Support.semisimple_allowed`, its evenness/range
hypotheses and the actual representation. Construct a distinct module carrier
with one additive/module/action presentation, prove its representation
equivalence to the original source, construct a nonzero invariant coefficient
through that presentation, then transport the result to the original theorem.
Combine producer and consumer proofs while their field/action parameters are
abstract. A wrapper without an actual-source return theorem is not acceptance.

If this gate passes, apply the same connection to the lower-generation
consumer. ScalarBlock's alternative mass definition is a subsequent bounded
phase; preserve equality with the existing pullback form if pursued.
No derivative/IBP completeness implementation, new physical input, dependency
pin change, new axiom or audit exception is included.

Keep default Lean recursion/kernel limits. Operational ceiling for a named
trial is 16 GiB process RSS and 9 minutes; do not repeat the earlier larger-cap
route. Stop a route if its actual-source bridge cannot be checked within these
bounds or requires a new independent foundation. Keep passing reusable proofs,
remove failed trial edits and record the exact remaining consumer. Verify
focused targets, strict transitive audits, full `lake build`, layout and docs;
commit a reviewable result. A failed whole-project gate prevents integration.

## Implementation And Individual Gates

The distinct carrier and its linear/representation equivalence are implemented
in [CarrierPresentation](../../../Math/RepresentationTheory/CarrierPresentation.lean).
The abstract producer constructs an injection, transports it to the presented
field, constructs its invariant coefficient on carriers and returns it to the
specified original representation. The actual and presented representations
are separate explicit parameters; no definitional identification is assumed.

[SMQ18Support](../../../Physics/StandardModel/Operators/SMQ18Support.lean)
now has `PresentedField`, its action, dimension 36, determinant-one proof and
middle exterior self-duality. `actualFieldEquiv` and `actualQuarkEquiv` connect
the species-zero module dictionary to the original generation tensor. The
existing `semisimple_allowed` statement passes unchanged. Its focused build
completed successfully (4217 jobs).

[SMGenerationCoefficients](../../../Physics/StandardModel/Operators/SMGenerationCoefficients.lean)
keeps the presented field through the local coefficient connection and moves
the equality of exterior degrees while the outer slot count is still abstract.
The lower-generation consumer uses the actual species-zero action with an
explicit equivalence to the presentation. Matching the three local tensor
additive instances to the producer closes the remaining elaboration boundary.
`lake env lean Physics/StandardModel/Operators/SMLowerGenerationSupport.lean`
passes with the original public hypotheses and conclusions. Its n=6/12 and
lepton cases remain in the existing constituent route.

[ProjectedWeylMass](../../../Physics/FieldTheory/Mass/ProjectedWeylMass.lean)
defines the symmetric form from the heavy field/dual projection and proves its
equality with the split mass pullback. Its generic membership lemma consumes
a proved form equality and a zero projection, without specializing the full
mass argument inside the proof body. `StandardScalarBlock.embedding_mem_radical`
now uses this lemma and the existing coordinate theorem.
The guarded ScalarBlock build passed: 4082 jobs, 11.0 seconds, peak process RSS
4162684 KiB. The 16 GiB / 9 minute guards did not trigger. This measurement is
for that named run, not a general resource bound.

The actual `StandardSMUVMass` and generic `EquivariantWeylMassTransport` sources
are unchanged by this pilot. Alternative literal/generic constructions of a
replacement mass were tested but removed: direct construction timed out in the
kernel after 85.2 seconds; abstract construction reached the character theorem
but still timed out in about 60 seconds. No limit was increased. Preserving the
checked mass and using the projection form as an explicit bridge closed the
consumer. This introduces no new mass, external premise or physical assumption.

## Downstream Local-Kernel Connection

The first combined audit exposed another recursion failure in
`SMQ18LocalSupport.restricted_allowed`, followed by an independent concrete
kernel-equivalence conversion failure. Its abstract helpers now compose the
presented-generation producer with restricted coefficients and compose the
compact-to-kernel equivalences before specializing the slot count. A helper
that only consumed the already specialized Q18 coefficient still failed and
was replaced by this combined producer/consumer proof. The original public
statements, including arbitrary `delta` for restricted coefficients, remain
unchanged. The complete `SMQ18LocalSupport` file passes with default limits.

## Final Verification And Integration

The focused build of `AuditCarrierPresentation`, `AuditSMGenerationSupport`,
`AuditSMCarrierConnection`, `AuditSMStructuralSupport` and `AuditScalarBlockQque`
passes (4910 jobs): respectively 11, 9, 20, 354 and 83 strict transitive checks.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted; layer/import
guards remain active. Layout coverage passes for 2081 modules.
The full `LEAN_NUM_THREADS=4 lake build` passes (7569 jobs), including Math,
Physics and GUT. This closes the recorded whole-project compatibility gate.
Documentation/structural checks and parent integration are recorded in
[verification](verification.md) and the [dependency record](dependency-integration.md).
The dependency pins, public mathematical hypotheses and conclusions are
unchanged by this pilot. Derivative/IBP completeness and optional HTML generation
remain outside its result.
