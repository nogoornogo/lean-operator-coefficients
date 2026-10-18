# Input Construction

The core accepts supplied groups, actions, multiplicities and exchange-stable
support. These optional construction routes are not one mandatory input package.

| Task | Entry points |
| --- | --- |
| Algebraic hypotheses | [Math assumptions](Math/ASSUMPTIONS.md) |
| Actual fields and scope | [Physics assumptions](Physics/ASSUMPTIONS.md) |
| Specified VEV and flavor stabilizers | [GUT assumptions](GUT/ASSUMPTIONS.md#specified-vev-and-flavor-stabilizers), [flavor](Physics/assumptions/flavor-stabilizers.md#flavor-stabilizer-inputs) |
| Majorana/Takagi stabilizers | [Math assumptions](Math/ASSUMPTIONS.md#full-unitary-majorana-stabilizers-and-takagi-existence) |
| Multiplicity actions | [Centralizer](Math/MULTIPLICITY_CENTRALIZER.md), [characters](Math/CHARACTER_EXACT.md), [restriction](Math/CHARACTER_RESTRICTION.md) |
| Conjugation and spectrum | [Structural conjugation](Physics/STRUCTURAL_CONJUGATION.md), [two conjugations](Physics/TWO_CONJUGATIONS.md), [vectorlike spectrum](Physics/VECTORLIKE_SPECTRUM.md) |
| Supplied scalar and mass data | [Scalar mass](Physics/SCALAR_DEPENDENT_MASS.md), [Weyl/Yukawa](Physics/WEYL_YUKAWA.md) |
| Species-dependent light components | [Copy surplus](Math/SPECIES_COPY_SURPLUS.md), [actual-mass qque bridge](../applications/Physics/SPECIES_COPY_SURPLUS_QQUE.md) |
| Concrete field presentation | [SM branching](GUT/SM_BRANCHING.md), [SU(5) source](GUT/interfaces/su5-source.md) |
| Arbitrary-degree scalar eigenlines | [Full coefficient reduction](Math/HIGGS_EIGENLINE_REDUCTION.md); requires actual line representations, not an SM doublet coordinate |
| Single weak doublet with weak-singlet source | [All-degree reduction](Math/WEAK_SINGLET_HIGGS_REDUCTION.md); actual SU2 restriction and whole-source weak triviality |

Vacua and interactions are supplied, not dynamically selected. Each route keeps
its own finiteness, continuity and external-premise conditions.

- [Symmetric content descent interfaces](Math/SYMMETRIC_CONTENT_DESCENT.md): full-field typed reconstruction and separate block descent; the final join remains open.

- [Actual SU2 symmetric tensor decomposition](Math/SU2_SYMMETRIC_TENSOR_DECOMPOSITION.md): all-degree doublet/dual Clebsch-Gordan carrier equivalence.

- [Full Higgs coefficient connection](Math/FULL_HIGGS_COEFFICIENT_CONNECTION.md): original full scalar content, split powers and full-group weak constituents.

The [concrete-dossier index](../RETAINED_RESULTS.md) includes the role-based
results formerly documented in the history library, with their original limits.

## Additional dossier entry points

- [scalar-dependent-mass](Physics/interfaces/scalar-dependent-mass.md).
- [su5-embedding](GUT/interfaces/su5-embedding.md).
- [su5-matter](GUT/interfaces/su5-matter.md).
