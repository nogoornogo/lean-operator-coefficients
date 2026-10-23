# Shared Abelian selection-rule foundation

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED` for the extracted algebra/tensor statements and the
new normal-form lemmas. This is SU5-1 of the
[SU(5) plan](../../../../topics/su5-foundations/plans/SU5_FORMALIZATION.md), not its actual-representation source
bridge or final no-go theorem.

## 3. Definitions and conventions

### Weight and Field Conventions

`StandardAbelianCharge.normalizeWeight_eq_iff` proves

```text
normalizeWeight e = normalizeWeight f
  iff exists c : Z, e(i) = f(i) + c for every i.
```

`normalizeWeight_surjective` supplies every rank-four weight through its
canonical fifth-coordinate-zero representative. These are statements about
the integer lattice, not a new character-realization theorem. In particular,
five independent exponents cannot be treated as faithful coordinates on the
SU(5) torus. The separate residual-character coordinate is not quotiented
out along with the common diagonal direction.

The gauge convention is the covering product `SU(3) x SU(2) x Circle`, with
color first and integer hypercharge `6Y`. Operator slots use right-handed
`u_R`, `d_R`, and `e_R`; stored `up`, `down`, and `electron` charges refer to
their left-handed conjugates. The two charge tests are therefore
`2*k_Q-k_u-k_e` and `k_Q+k_L-k_u-k_d`. Their gauge hypercharges remain
`(1,4,-2,-3,-6)` for `(Q,u_R,d_R,L,e_R)`.

## 5. Lean entry points

### Independent Modules

| Module | Responsibility |
| --- | --- |
| `Math/RepresentationTheory/Characters/AbelianCharge.lean` | Circle-valued group characters as additive charge labels |
| `Physics/StandardModel/Operators/Selection/AbelianProtonCharge.lean` | Five field charges and two proton-operator charge functionals |
| `Physics/StandardModel/Operators/Selection/AbelianProtonCharacter.lean` | Evaluation of those functionals as residual characters |
| `Math/LieGroups/SpecialUnitary/RankFive/WeylOrbit.lean` | Permutations of five raw exponents |
| `Physics/StandardModel/Spectrum/Charges/ChargeResolved.lean` | Rank-four normal form, independent charge labels, coefficient profiles and support |
| `Physics/StandardModel/Operators/Selection/StandardModelLocalOperator.lean` | Supported dimension-six signatures and charge tests |
| `Physics/StandardModel/Gauge/Tensors/SMEpsilonTensor.lean` and `StandardSMGaugeTensor.lean` | Actual ordered internal gauge tensors |
| `Physics/StandardModel/Gauge/Tensors/ResidualGaugeTensor.lean` | Residual transformation laws and conditional invariant tensors |

These modules have no transitive SU(6) imports. Existing declaration
namespaces, including `GUT.FiniteAbelianChargeSectors` and
`GUT.StandardSMResidualTensor`, are retained to preserve consumers; those
names do not themselves assert a finite group or an SU(6) representation.

`protonCharacters_eq_one_of_su5OrbitCompatible` and
`invariant_tensors_of_su5OrbitCompatible` combine the charge algebra with the
actual tensor transformation laws for any commutative group `H`. They are
conditional on multiplet-compatible charges. Deriving that compatibility
from an actual SU(5) matter action remains SU5-3/4, not an assumed bridge.
No continuous-anomaly theorem occurs in the shared dependency closure.

## 6. Scope and limitations

### Compatibility Boundary

- `GUT/SU6/Branching/StandardSU5Orbit.lean` re-exports the raw orbit algebra.
- The old `StandardAbelianCharge` source module re-exports the new coefficient
  core and retains the actual ambient SU(6) adapters.
- `FiniteAbelianChargeSectors` retains the commuting SU(6) source and sector
  construction, re-exporting the independent character definitions.
- `StandardBranchProtonObstruction` retains the separate rational anomaly
  cross-check while importing the shared Abelian charge algebra.
- `GUT/SU6/Adapters/StandardSMResidualTensor.lean` is a **legacy SU(6)
  entry point**: it still supplies `source_invariant_tensors` for the actual
  SU(6) source. New independent consumers import `ResidualGaugeTensor`.
- `StandardSMContragredient` and `StandardSMExterior` still contain
  six-dimensional branching. They are not included in this independent
  module boundary and are not silently reused as five-dimensional proofs.

No old declaration was removed or weakened. Ordered internal tensor
nonvanishing still does not prove nonvanishing after the Lorentz/Grassmann
quotient or a nonzero interaction coefficient or amplitude.

## 7. Sources and verification

### Persistent Audit

`Physics/StandardModel/Operators/Selection/Audit/AuditSharedSelectionRules.lean` checks the actual
transitive Lean environment and fails compilation if a `GUT.SU6` module is
imported. It retains the finite sign-character positive/negative tensor
tests and adds the nontriviality of that character, collapse of the raw
diagonal shift, survival of the independent residual label, and hypercharge
sign conventions. Audited statements use only a subset of `propext`,
`Classical.choice`, and `Quot.sound`.

The old SU(6) tensor audit imports this shared audit and additionally checks
the original physical-source specialization. Both are included in `GUT.lean`.

```sh
lake build Physics.StandardModel.Operators.Selection.Audit.AuditSharedSelectionRules
lake build GUT.SU6.SelectionRules.Audit.AuditStandardSMGaugeTensor
lake build
```

Verification at stage 01: the standalone shared build passed (3087 jobs),
the combined shared/legacy audit passed (3935 jobs), and the full regression
passed (4262 jobs). The latest completed full regression is
recorded in [historical verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).

The SU5-3a extension also extracts `StandardModel.WeakContragredient` and
`StandardModel.ExteriorPairing`: the weak epsilon duality and charged
color/weak/mixed covariance identities now have SU(6)-free imports. Their
old public names are preserved for the six-dimensional branching adapters.
The [matter audit](../../inputs/GUT/interfaces/su5-matter.md) checks the extended import
boundary; the actual SU(6) branching modules themselves remain separate.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
