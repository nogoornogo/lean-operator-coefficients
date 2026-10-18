# Compact Spin chain implementation

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The actual SU(5) inclusion
into compact Spin(10) is continuous, injective and closed; the common
conditional selection-rule adapter is checked.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Updated: stage 01

## 2. Inputs And Conclusion

The topology of actual SU groups supplies the lift hypotheses; model-level mass
and positive-target premises remain explicit.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Realification, source simple connectedness and the Spin covering lift give the
inclusion; common-chain pullback supplies the model endpoint.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declarations

- [CoveringHom](../../../../../../Math/Topology/CoveringHom.lean): unique continuous
  homomorphism lift from a simply-connected, locally path-connected group;
  injectivity inherited from the projected map.
- [SpecialUnitaryRealification](../../../../../../Math/LieGroups/SpecialUnitary/SpecialUnitaryRealification.lean):
  real coordinates, preserved positive form, real determinant one, and the
  continuous injective closed embedding SU(n) -> SO(2n), including n = 0.
- [CompactGroup](../../../../../../Math/LieGroups/Spin/CompactGroup.lean): pinned actual compact
  real Spin carrier and projection, surjectivity, covering property, exact
  two-element fibers, noninjective projection, compactness, path-connectedness.
- [CoveringLift](../../../../../../Math/LieGroups/Spin/CoveringLift.lean): the generic lift specialized
  to the actual Spin double cover, with source topology premises explicit.
- [SpecialUnitaryConnected](../../../../../../Math/Topology/SpecialUnitaryConnected.lean):
  continuous determinant-correcting retraction U(n) -> SU(n), its quotient
  property, and local path-connectedness of SU(n) for every n.
- [VectorStabilizer](../../../../../../Math/LieGroups/SpecialUnitary/VectorStabilizer.lean): the actual
  last-vector stabilizer in SU(n+1) is topologically group-isomorphic to
  SU(n) by the existing block inclusion; the inverse extracts the upper block.
- [SphereSection](../../../../../../Math/LieGroups/SpecialUnitary/SphereSection.lean): continuous
  last-column projection to the Euclidean unit sphere, explicit unitary
  rank-one sections, right determinant correction, two covering patches,
  continuous SU-valued sections, and surjectivity for rank at least two.
- [SphereLocalProduct](../../../../../../Math/LieGroups/SpecialUnitary/SphereLocalProduct.lean): a
  section gives a homeomorphism with the actual stabilizer product;
  `exists_localProduct` supplies an open product neighborhood with SU(m-1)
  at every point of the base of SU(m), m >= 2. No global product or
  homotopy-lifting theorem is asserted.
- [SU5LiftPreparation](../../../../../../Math/LieGroups/Spin/SU5LiftPreparation.lean): unconditional
  SU(5) -> SO(10) closed embedding, proved local path-connectedness, and
  `exists_SU5_inclusion_of_simplyConnected`. This compatibility interface
  retains its explicit premise; the module below discharges it. The original
  two-premise lift interface is preserved.
- [PuncturedSphere](../../../../../../Math/Topology/PuncturedSphere.lean): the two-pole
  complement is path connected above real dimension two, via stereography.
- [SimplyConnectedUnion](../../../../../../Math/Topology/SimplyConnectedUnion.lean):
  finite path subdivision and two-open-set simple-connectedness gluing.
- [SpecialUnitaryBase](../../../../../../Math/LieGroups/SpecialUnitary/SpecialUnitaryBase.lean),
  [SpherePatchTopology](../../../../../../Math/LieGroups/SpecialUnitary/SpherePatchTopology.lean), and
  [SimplyConnected](../../../../../../Math/LieGroups/SpecialUnitary/SimplyConnected.lean): the actual
  SU(1) base case, contractible chart domains, fiber homotopy equivalences,
  path-connected overlap, and simple-connectedness of every actual SU(n).
  This discharges the mathematical topology obligation.
- [SU5Inclusion](../../../../../../Math/LieGroups/Spin/SU5Inclusion.lean): `SU5Inclusion` and
  `continuousSU5Inclusion`, unconditional continuity, injectivity, closed
  embedding, `projection_comp_SU5Inclusion`, and uniqueness among continuous
  homomorphic lifts of the actual realification map.
- [StandardChain](../../../../../../GUT/Spin10/SelectionRules/StandardChain.lean):
  `Model`, `selection_rule_obstruction`, `continuousModel`,
  `continuous_selection_rule_obstruction`, and the corresponding scalar-family
  model, endpoint, and continuous adapter. These reuse the common theorem;
  an actual positive-target model is constructed separately in
  `HalfSpinBenchmark`. The [SPIN-2 record](spin-half-spin.md) constructs
  the continuous unitary 16, proves its all-SU(5) character `1 + 10 + bar5`,
  and derives the light target and full spectrum for the zero-mass example.

## 6. Scope And Limitations

The inclusion alone is not a half-spin model inhabitant or a dynamically selected vacuum.

## 7. Sources And Verification

The [scope dossier](../SPIN_STANDARD_CHAIN.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Verification

```sh
lake build Math.LieGroups.Spin.Audit.AuditSU5Inclusion \
  GUT.Spin10.Audit.AuditStandardChain
lake build
```

SPIN-1 checkpoint: targeted **4112 jobs / 26 axiom reports**; full
**4614 jobs / 1900 axiom reports**. Only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`. New modules/audits are warning-free; existing
full-build linter warnings remain. Dependency pins are unchanged.

Previous SPIN-1d checkpoint: targeted **3256 jobs / 25 axiom reports**; full
**4610 jobs / 1883 axiom reports**. Only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`. New files are warning-free; existing full-build
linter warnings remain. Dependency pins are unchanged.

Previous SPIN-1c checkpoint: targeted **3496 jobs / 39 axiom reports**; full
**4594 jobs / 1858 axiom reports**. New modules/audits are warning-free;
the full build retains pre-existing linter warnings. Only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx`. Dependencies unchanged.

Previous SPIN-1b checkpoint: targeted **3495 jobs / 39 axiom reports**; full
**4591 jobs / 1837 axiom reports**. New modules/audits are warning-free;
the full build retains pre-existing linter warnings.
Only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.

Previous SPIN-1a checkpoint: targeted **3084 jobs / 25 axiom reports**; full
**4587 jobs / 1814 axiom reports**. Only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`. Dependency versions remain unchanged.

[AuditCompactSpin](../../../../../../Math/LieGroups/Spin/Audit/AuditCompactSpin.lean) checks the actual
rank-ten carrier and projection and rejects SU(5)/SU(6)/USp imports.
[AuditSpecialUnitaryRealification](../../../../../../Math/LieGroups/SpecialUnitary/Audit/AuditSpecialUnitaryRealification.lean)
checks real/imaginary coordinate order, ranks zero and one, and a nontrivial
SU(2) matrix whose realification is nontrivial. Its import guard rejects
concrete GUT-family modules. Both audits are in the default build.

[AuditSpecialUnitaryConnected](../../../../../../Math/Topology/Audit/AuditSpecialUnitaryConnected.lean)
checks ranks zero, one, and five and an explicit failure of multiplicativity
of the retraction. [AuditVectorStabilizer](../../../../../../Math/LieGroups/SpecialUnitary/Audit/AuditVectorStabilizer.lean)
checks the inverse block map, the empty-rank case, and an SU(2) rotation
outside both the stabilizer and the block image. Both reject concrete-family
imports and are included in the default build.

[AuditSphereLocalProduct](../../../../../../Math/LieGroups/SpecialUnitary/Audit/AuditSphereLocalProduct.lean)
checks both patches, reaching a point excluded from the north patch,
an off-axis unit vector, both directions of the chart identities, ranks
two and five, and failure of surjectivity at rank one. It rejects concrete
SU(5)/SU(6)/USp/Spin imports and is included in the default build.

[AuditSimplyConnected](../../../../../../Math/LieGroups/SpecialUnitary/Audit/AuditSimplyConnected.lean) checks
the topology at ranks 0, 1, 2, and 5 and the overlap construction.
[AuditSimplyConnectedUnion](../../../../../../Math/Topology/Audit/AuditSimplyConnectedUnion.lean)
tests real-line gluing and a discrete two-point counterexample without a
nonempty overlap. Both audits enforce group-family import boundaries and
are included in the default build.

[AuditSU5Inclusion](../../../../../../Math/LieGroups/Spin/Audit/AuditSU5Inclusion.lean) verifies the
unconditional source topology, projection identity, unique lift, closed
embedding, and a nonidentity image. It forbids SU(5) matter, SU(6), and USp
imports. [AuditStandardChain](../../../../../../GUT/Spin10/Audit/AuditStandardChain.lean)
allows the common SU(5) source theory but rejects SU(6)/USp dependencies;
it checks the finite residual group Z/3 and continuous circle interfaces
with explicit model inputs. These are not half-spin model inhabitants.
Both audits are in the default build.

Full claim boundaries and the separate actual half-spin model are in the
[Spin dossier](../SPIN_STANDARD_CHAIN.md).
