# E6 Candidate SU(5) Group Map

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Result

**The bounded group-map package is complete.**
[SU5Inclusion](../../../../../GUT/E6/Minuscule/SU5Inclusion.lean) constructs
`continuousInclusion : SU5 →ₜ* compactIdentityComponent`. The underlying
`inclusion` is injective and a closed topological embedding. Its definition
takes no inclusion or exponential-compatibility certificate.

The proof has four finite interfaces:

- [SU5GroupAction](../../../../../GUT/E6/Minuscule/SU5GroupAction.lean) transports the
  actual scalar, defining, dual and exterior-square representations through
  the already checked signed coordinates. The defining block proves
  faithfulness; the matrix-entry formulas prove continuity.
- [SU5Exponential](../../../../../GUT/E6/Minuscule/SU5Exponential.lean) computes the
  initial derivative on every compact SU(5) direction. TauCeti's existing
  one-parameter uniqueness theorem then proves represented-exponential
  compatibility for every real time, not only simple generators.
- [SU5LieImage](../../../../../GUT/E6/Minuscule/SU5LieImage.lean) expresses the 20
  off-diagonal and four diagonal trace-zero basis directions in the already
  checked E6 matrix basis. The integer coefficient table is kernel-checked.
  Complex linearity and preservation of adjoints put every compact SU(5)
  direction in the actual real E6 matrix Lie algebra.
- `SU5Inclusion` combines this with the existing all-time exponential
  criterion and the proved two-exponential factorization of SU(5).
  Thus every group element belongs to the candidate's identity component.
  `inclusion_intertwining` proves the actual group restriction
  `1 + 1 + 5 + bar5 + bar5 + wedge^2(5)`, not just a character count or
  infinitesimal comparison.

The [persistent audit](../../../../../GUT/E6/Audit/AuditSU5Inclusion.lean) also
instantiates the common continuous standard-chain interface using the
proved injectivity/continuity, and checks its selection-rule consumer.
Mass, residual-action and exact light-target hypotheses are still required.
This is not an inhabitant of that model class or a new named-E6 endpoint.

## 5. Lean entry points

### Bounded Implementation

The user approved continuing the remaining proofs after `checkpoint 01`.
Consumer: the existing common continuous standard-chain selection rule,
specialized to `compactIdentityComponent`, not silently renamed compact E6.

The target is an actual continuous injective SU(5) homomorphism into that
candidate. Its coordinate action must be the scalar/defining/dual/exterior
action from [the completed coordinate comparison](E6_SU5_COORDINATES.md).

1. `SU5GroupAction`: construct the actual action and matrix homomorphism;
   prove continuity, faithfulness and explicit coordinate formulas.
2. Prove represented-exponential compatibility using the concrete
   derivative and the existing one-parameter subgroup classification.
3. Prove that compact SU(5) directions map into the existing real E6 matrix
   algebra; use finite matrix checks and the already checked basis/closure.
4. Use the existing finite-product exponential generation to obtain
   subgroup membership and bundle the actual continuous injective map.

Local helpers for these interfaces are allowed. No general Lie integration,
center classification, simple connectedness, dependency changes or supplied
compatibility certificates are authorized. Stop at the actual map and its
audit, or report a precise obstruction to this concrete route. A positive
target inhabitant and named global E6 identification remain separate tasks.

## 7. Sources and verification

### Verification and Stop

```sh
lake build GUT.E6.Audit.AuditSU5Inclusion
lake build
```

The focused audit checks 31 declarations against only `propext`,
`Classical.choice` and `Quot.sound`; 4409 jobs. It includes actual group
intertwining, all-time exponential compatibility, a trace-zero boundary
control and the existing conditional selection-rule consumer. Full-build
results are recorded in [historical milestone record](../../../../topics/e6-global-topology/checkpoints/e6-sources.md).
No new dependency, axiom, external calculation or assumed compatibility is
trusted. The finite coefficient table is in Lean; exploratory JSON files
are not build inputs.

The agreed stop checkpoint is reached. The actual SU(5) candidate-group map
and its group-action comparison are proved. Identifying the carrier with
the intended global compact E6 and constructing an actual positive-target
27 model remain separate, unproved deliverables. No exact center, simple
connectedness, general integration, vacuum dynamics or amplitude claim is
added; the completed feasibility audit is not reopened.

The subsequent bounded [positive-target model](E6_POSITIVE_TARGET.md) now
constructs the actual continuous unitary 27 source and a zero-mass
inhabitant with derived positive dual index on this candidate. Global E6
identification remains open; it was not part of either bounded package.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
