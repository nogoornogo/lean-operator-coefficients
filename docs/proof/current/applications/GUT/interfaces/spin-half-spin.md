# Compact half-spin implementation

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The actual continuous
unitary half-spin 16 has the stated SU(5) character and a constructed
positive-target zero-mass model.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Updated: stage 01

## 2. Inputs And Conclusion

The even exterior/Clifford construction uses the actual compact Spin carrier;
the benchmark has trivial residual action and zero mass.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Clifford covariance identifies the SU(5) exterior action; even-degree trace sums
give branching and the benchmark target.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declarations

- [PolarizedClifford](../../../../../../Math/LieGroups/Spin/PolarizedClifford.lean): the real-linear
  `coordinates`, injectivity, `coordinates_form`, the real-to-complex
  `cliffordMap`, preservation of even degree, and `evenMap`.
- [HalfSpin](../../../../../../Math/LieGroups/Spin/HalfSpin.lean): `algebraAction`, the actual
  compact `representation`, `polarization_finrank`, `finrank`, and
  `finrank_sixteen`; coefficient continuity; `HilbertSpace`, `unitaryModel`,
  its unitarity and joint continuity, `unitaryModelEquiv`, equality of
  characters, and `hilbert_finrank_sixteen`.
- The same module constructs `centralNegOne`, proves it projects to one
  but acts as `-Id`, proves `not_descends_to_SO`, and computes the algebraic
  and unitary characters at that element as `-16`.
- [ExteriorNaturality](../../../../../../Math/LinearAlgebra/ExteriorNaturality.lean)
  and [PolarizedExteriorAction](../../../../../../Math/LinearAlgebra/PolarizedExteriorAction.lean):
  exterior functoriality intertwines creation and contraction, with the
  inverse covector action; these modules do not import a gauge family.
- [CliffordCovariance](../../../../../../Math/LieGroups/Spin/CliffordCovariance.lean): the full
  `Fock.representation`, coefficient continuity, actual Spin generator
  conjugation, `SU5_conjugation`, and restriction to the even spinors.
- [ExteriorComparison](../../../../../../Math/LieGroups/Spin/ExteriorComparison.lean): explicit W
  coordinates, actual defining SU action and dual action, compatibility
  with realification, and exterior `generator_naturality`.
- [PolarizedSpan](../../../../../../Math/LieGroups/Spin/PolarizedSpan.lean) and
  [FockCommutant](../../../../../../Math/LieGroups/Spin/FockCommutant.lean): complex spanning by real
  generators and `commutant_scalar`, using the full Clifford action.
- [SU5ScalarComparison](../../../../../../Math/LieGroups/Spin/SU5ScalarComparison.lean): the actual
  comparison operator, its scalar coefficient, `scalarHom`, and continuity.
- [CompactCharacters](../../../../../../Math/Topology/CompactCharacters.lean): compact
  real characters vanish; compact complex characters have modulus one;
  simple connectedness and local path-connectedness make the circle and
  complex characters trivial, by the exponential covering lift.
- [SU5ExteriorAction](../../../../../../Math/LieGroups/Spin/SU5ExteriorAction.lean): `scalar_eq_one`,
  `actual_eq_exterior`, `halfSpin_eq_exterior`, and `actual_fixes_vacuum`.
  The last refers to the Fock algebra unit, not a Higgs vacuum.
- [UnitaryEigenbasis](../../../../../../Math/RepresentationTheory/Unitary/UnitaryEigenbasis.lean):
  `exists_character_basis` for an Abelian unitary action and
  `exists_element_basis` for one element of an arbitrary unitary group
  action, by cyclic restriction. No spectral certificate is an input.
- [ExteriorEigenbasisTrace](../../../../../../Math/LinearAlgebra/ExteriorEigenbasisTrace.lean):
  the new `algebra_eigen` extends the existing exterior-power trace API to
  the full exterior algebra basis.
- [RankFiveExteriorSum](../../../../../../Math/LinearAlgebra/RankFiveExteriorSum.lean):
  `by_degree`, `degree_four`, and `determinant_one` split the even subset sum
  into degrees 0/2/4 and identify degree 4 with inverse weights.
- [HalfSpinEigenbasis](../../../../../../Math/LieGroups/Spin/HalfSpinEigenbasis.lean): 16 independent
  even exterior vectors form a `basis` of the actual half-spin space;
  `eigen` and `character` compute the action and trace in that basis.
- [SU5Branching](../../../../../../GUT/Spin10/SU5Branching.lean):
  `exists_fundamental_eigenbasis`, `product_eigenvalues`,
  `halfSpin_character`, `unitary_character`, and `unitary_dual_index`.
  The last three have only the actual SU(5) element as input and prove
  oriented branching and singlet cancellation on the entire group.
- [HalfSpinBenchmark](../../../../../../GUT/Spin10/SelectionRules/HalfSpinBenchmark.lean):
  actual `rho` with `residual_trivial`, positive `family`, and one neutral
  `singlets`; `restricted_character` and `restricted_dual_index` derive
  the physical target. `hasTarget` works for any invariant symmetric mass
  on this restriction. `model` and `continuousModel` choose zero mass.
  `radicalEquiv`, `radical_character`, and `lightSpectrum_eq` prove the exact
  full spectrum of that choice; `radical_finrank` is 16,
  `light_index_coefficient` is 1 at each SM weight, and
  `light_singlet_coefficient` is 1. `exists_sm_zeroMode` provides actual
  nonzero radical witnesses; `nonvacuous` applies the common obstruction.
- [TorusMassSource](../../../../../../GUT/SU5/SelectionRules/TorusMassSource.lean):
  the reusable `spectrum_eq_of_character` deduces full resolved spectrum
  equality from an actual radical trace identity. Unlike `chiral_spectrum`,
  it requires a full character identity, not just the dual target.

These use the existing actual `CompactSpin.Group (n+n)`, not a newly
postulated carrier. The source topology and all TauCeti/mathlib pins are
unchanged. The unitary model uses the existing group-independent
[FiniteBasisUnitaryModel](../../../../../../Math/RepresentationTheory/Unitary/FiniteBasisUnitaryModel.lean).

## 6. Scope And Limitations

Character branching is not an explicit direct-sum intertwiner here; realistic
masses and exact-SM vacuum dynamics are not claimed.

### Scope After SPIN-2

This constructs the compact even exterior spinor model and identifies its
actual SU(5) restriction exactly with the exterior action, then proves the
oriented character `1 + 10 + bar5` and constructs an actual positive-target
continuous model. SPIN-2 is complete in the approved zero-mass, trivial
residual-action scope. An explicit direct-sum intertwiner, compact
irreducibility, realistic masses, and a dynamically selected exact-SM
vacuum are not claimed or required by this gate; see
[the proof dossier](../SPIN_HALF_SPIN.md).
The [Spin chain record](spin-chain.md) covers the already constructed actual
SU(5) inclusion and its conditional selection-rule endpoint.

## 7. Sources And Verification

The [scope dossier](../SPIN_HALF_SPIN.md) supplies related statement and hypothesis context;
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
lake build Math.LieGroups.Spin.Audit.AuditHalfSpin
lake build Math.LieGroups.Spin.Audit.AuditSU5ExteriorAction Math.LinearAlgebra.Audit.AuditExteriorNaturality Math.Topology.Audit.AuditCompactCharacters
lake build GUT.Spin10.Audit.AuditSU5Branching Math.RepresentationTheory.Unitary.Audit.AuditUnitaryExteriorTrace
lake build GUT.Spin10.Audit.AuditHalfSpinBenchmark
lake build
```

SPIN-2a checkpoint: targeted **3511 jobs / 23 axiom reports**; full
**4625 jobs / 1923 axiom reports**. Only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`. New files are warning-free. Existing linter
warnings in reused Hilbertization and other modules remain unchanged.

[AuditHalfSpin](../../../../../../Math/LieGroups/Spin/Audit/AuditHalfSpin.lean) checks dimensions
at n = 1 and 5, continuity at n = 0 and 5, the positive imaginary-axis
quadratic value, and the nontrivial central character. Its import guard
rejects SU(5) matter, SU(6), and USp dependencies. It is in the default build.

The exterior-comparison checkpoint adds three default-build audits:
[AuditExteriorNaturality](../../../../../../Math/LinearAlgebra/Audit/AuditExteriorNaturality.lean),
[AuditCompactCharacters](../../../../../../Math/Topology/Audit/AuditCompactCharacters.lean),
and [AuditSU5ExteriorAction](../../../../../../Math/LieGroups/Spin/Audit/AuditSU5ExteriorAction.lean).
They check inverse-versus-forward covectors on a dilation, the zero-rank
commutant, the scalar-conjugation ambiguity, nontrivial characters without
the needed topology, and the exact full/even action comparison. Separate
import guards isolate generic results from gauge families and the Spin
comparison from SU(5) matter/SU(6)/USp dependencies.

SPIN-2b exterior-comparison checkpoint: targeted **3788 jobs / 38 axiom
reports**; full **4637 jobs / 1962 axiom reports**. Every reported axiom is
`propext`, `Classical.choice`, or `Quot.sound`; no `sorryAx`. The new modules
are warning-free; existing unrelated linter warnings are unchanged.

SPIN-2b character-branching milestone: targeted **4133 jobs / 22 axiom
reports**; full **4643 jobs / 1984 axiom reports**, again with only
`propext`, `Classical.choice`, and `Quot.sound`. The new and extended
modules are warning-free. Two new default-build audits are
[AuditUnitaryExteriorTrace](../../../../../../Math/RepresentationTheory/Unitary/Audit/AuditUnitaryExteriorTrace.lean)
and [AuditSU5Branching](../../../../../../GUT/Spin10/Audit/AuditSU5Branching.lean).
They check empty/repeated eigenvalues, a determinant-not-one counterexample,
all-element branching, and an actual diagonal SU(5) control distinguishing
`bar5` from `5`. The generic audit excludes every current gauge family;
the branching audit intentionally allows SU(5) matter but excludes SU(6)/USp.

SPIN-2c actual-model milestone: targeted **4191 jobs / 28 axiom reports**;
full **4645 jobs / 2012 axiom reports**, with only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx`. New and extended modules
are warning-free; unrelated existing linter warnings remain. The
default-build [AuditHalfSpinBenchmark](../../../../../../GUT/Spin10/Audit/AuditHalfSpinBenchmark.lean)
constructs continuous Z/3 and Circle models, checks physical-torus target
compatibility, the 16-dimensional radical, actual SM mode support, the
present but dual-index-invisible singlet, and exclusion of zero/negative
generation interpretations. Its import guard rejects SU(6), USp, and
SU(n) no-go models; shared SU(n) block/topology prerequisites remain allowed.
