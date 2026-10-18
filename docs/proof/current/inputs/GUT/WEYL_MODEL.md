# Symmetric linearized mass model

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED`, including continuous geometry, arbitrary integral
cocharacters, finite Abelian residual groups, actual radical support, and
a one-generation non-vacuity constructor. The original milestone build had
4203 jobs; see the [verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md)
for the current full build.

This dossier describes the retained **fixed-charge** interface with a
**nonzero integer generation parameter**, still using the dual radical index.
The [profile extension](../../applications/GUT/PROFILE_MODEL.md) now removes its single-charge
restriction for positive generation totals, and the
[scalar-family extension](../../applications/GUT/SCALAR_DEPENDENT_MODEL.md) removes scalar-linearity
from the source wrapper. `ContinuousProfileModel.ScalarModel` combines both.
Negative-orientation profiles and nonlinear Dirac wrappers are not asserted.

## 4. Proof structure

### Derived chain

1. The existing continuity-only semisimple embedding classification and centralizer lattice construct the
   canonical cocharacter pair from geometry.
2. `PhysicalWeylMassSource.fields_character` derives the actual UV trace
   from full residual-charge sectors and nonnegative multiplicities. No
   Laurent model or UV trace-identification field is assumed.
3. Radical dual-index conservation and faithful evaluation derive one
   charge-resolved physical dual target at that pair.
4. `PhysicalWeylMomentBridge` proves that antisymmetrization doubles the
   odd fifth moment. The target therefore feeds hypercharge character rigidity and forces `(-2,3)`.
5. `PhysicalWeylChargeBridge` transports the **same** dual target through
   the injective standard-key embedding. standard charge-orbit bridge gives `k_Q = k_u = k_e` and
   `k_d = k_L`; Abelian proton-operator neutrality gives neutral proton operator characters. Torsion charges
   are retained, and continuous U(1) anomaly cross-check is not used.
6. `PhysicalWeylZeroModeSupport` constructs nonnegative actual radical
   multiplicities. Positive index forces every oriented SM sector to have
   a nonzero zero-mode vector; negative index forces its conjugate.
7. `ContinuousWeylMassModel.supportedInvariantOperator` supplies `qque`
   for positive index. For arbitrary nonzero index,
   `exists_invariant_operator_or_conjugate` and `not_forbidsBothOrientations`
   distinguish the two signatures explicitly. The conjugate has inverted
   residual character and opposite baryon number, not a relabelled positive
   signature.

This is a separate checked extension of the scoped theorem to the declared finite-dimensional
symmetric linearized model class. Existing Dirac/Yukawa theorems and the
independent flipped obstruction remain unchanged.

## 6. Scope and limitations

### Model boundary

`ContinuousWeylModel.ContinuousWeylMassModel H` records:

- continuous injective `SU(3) x SU(2) -> SU(6)` geometry and an injective
  commuting continuous hypercharge circle;
- a finite list of actual continuous-unitary SU(6) matter representations,
  nonnegative copy multiplicities, and strict commuting unitary Abelian
  residual actions;
- a complex-bilinear symmetric mass on the canonical all-left-handed
  fields, invariant under the physical four-torus times H;
- a nonzero integer generation index, residual charge assignments, singlets,
  and an exact **dual** SM target for the actual mass radical.

The target is `[rad B] - [(rad B)*] = T - T*`, as an equality of actual
characters. It is an infrared applicability condition, not a conclusion
about every Lagrangian. It neither fixes self-dual singlets nor excludes
additional vectorlike zero modes. In particular this index must not be
identified with the signed Dirac kernel/cokernel index.

The mass interface only requires torus-times-H invariance. The separate
[symmetric Yukawa adapter](../Physics/WEYL_YUKAWA.md) now derives this mass from a
scalar-linear invariant coupling and a fixed VEV, including actual
mass/Yukawa tensors for arbitrary groups. That adapter remains a special
case of the checked jointly continuous equivariant mass families; nonlinear
scalar dependence still leaves the fermion coefficient bilinear.
The proton operator itself still
uses the existing EFT signature API, not a full non-Abelian tensor on the
radical. No general Lagrangian semantics, second-quantized operator algebra,
or nonzero Wilson coefficient is added.

## 7. Sources and verification

### Non-vacuity and audits

`ContinuousWeylBenchmark.model H` constructs one generation from actual
`15 + 2 bar6` with neutral residual action and continuous standard geometry.
Its mass is zero. `ofStandardWithZeroMass` transports the independently
proved UV dual target from a fixed-standard model; it does **not** claim
to transport that model's mass or radical. Thus the new interface is inhabited
without a spectrum or model premise, including for `Multiplicative (ZMod 2)`.

Separately, the retained fixed-standard `ConcreteWeylFullMass.model H` has
nonzero mass, radical dimension 15, and exact full SM character. Its six
paired sectors include the neutral singlets. `StandardWeylFieldIdentification`
now proves equality of the actual bundled field constructions, not just
their characters. `ContinuousWeylMassTransport.ofStandard` transports the
given mass along this equality. `mass_heq`, `radicalEquiv`, and `actualSpectrum`
prove preservation of the mass, radical representation, and full spectrum.
`ContinuousWeylFullMass.model H` consequently has nonzero mass and exactly
15 SM zero modes in the continuous-geometry interface. The earlier zero-mass
constructor is retained. `AuditContinuousWeylFullMass` checks this stronger
constructor and standard axioms for trivial and finite Abelian residual H.

`AuditPhysicalWeylChargeBridge` and `AuditContinuousWeylModel` are imported
by the default build. They check constructors, torsion specialization,
actual nonzero radical vectors, and the endpoint axiom dependencies:
only `propext`, `Classical.choice`, and `Quot.sound`. No new axiom or
`sorry` is used.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
