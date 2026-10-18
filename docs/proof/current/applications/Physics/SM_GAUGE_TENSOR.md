# Standard Model gauge tensors

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: `LEAN-CHECKED` for nonzero ordered internal gauge tensors on the
standard field representations, including their residual Abelian action.
This is the first tensor-extension milestone, not the mass-radical bridge.
Full build: 4203 jobs.

This opening status and build count record the original milestone. The newer
[explicit SM x H construction](EXPLICIT_SM_RESIDUAL_TENSOR.md) handles arbitrary
H-invariant multiplicity coefficients, including non-Abelian H. Its compact
source adapter reaches actual light-field subspaces under additional compatible
full-SM decompositions; no automatic extension from torus data is claimed.

## 3. Definitions and conventions

### Actual spaces and actions

`StandardSMGaugeTensor` uses the covering product
`SU(3) x SU(2) x U(1)`. Color and weak vectors carry the actual defining
matrix representations. The integral hypercharge convention is `6Y`:

| Physical field | Internal vector space | 6Y |
| --- | --- | --- |
| Q | C^3 tensor C^2 | 1 |
| u_R | C^3 | 4 |
| d_R | C^3 | -2 |
| L | C^2 | -3 |
| e_R | C | -6 |

The right-handed convention is the same as `StandardModelLocalOperator`;
their residual charges are negatives of the stored left-handed conjugates.
No assertion about the global quotient of the covering group is needed here.

`SMEpsilonTensor` supplies the color determinant and weak determinant as
linear maps on their tensor products. Tensor associators and permutations
assemble two actual linear maps:

```text
qque : (Q tensor Q) tensor (u_R tensor e_R) -> C
duql : (d_R tensor u_R) tensor (Q tensor L) -> C
```

Their values on decomposable vectors are respectively
`eps3(a,b,c) * eps2(x,y) * e` and `eps3(a,b,c) * eps2(x,y)`.
`qqueIntertwiner` and `duqlIntertwiner` prove invariance under every element
of the full covering gauge group. The proofs extend from decomposable
vectors by tensor-product linearity. Explicit witnesses evaluate to one,
so neither map is zero.

## 4. Proof structure

### Residual symmetry and Abelian proton-operator neutrality

`ResidualGaugeTensor` (retaining the `StandardSMResidualTensor` declaration
namespace) gives each field its declared residual character
and constructs the tensor-product action of `GaugeGroup x H`, for any
commutative group `H`. It proves the exact transformation laws

```text
qque(rho(g,h) x) = protonFirstCharacter(k,h) * qque(x)
duql(rho(g,h) x) = protonSecondCharacter(k,h) * duql(x).
```

For each tensor, invariance is equivalent to triviality of that character.
The reverse direction uses the nonzero witness, not an assumption that the
map is nonzero. `source_invariant_tensors` applies the already checked
standard charge-orbit bridge -> Abelian proton-operator neutrality result to obtain both invariant nonzero tensors on these standard
spaces. No continuous anomaly argument is used; finite groups are included.

`AuditStandardSMGaugeTensor` checks a nontrivial sign character of the
two-element group of integer units. A standard charge-orbit bridge-compatible charge assignment gives
both invariant tensors. A deliberately incompatible assignment changes
each witness value from one to minus one. This negative test ensures that
residual invariance is not obtained for arbitrary charges. The persistent
axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The group-independent tests now live in `AuditSharedSelectionRules`, whose
transitive environment is checked to exclude SU(6). The old audit imports
these tests and additionally checks the physical-source theorem.
`StandardSMResidualTensor.lean` remains a legacy entry point for that SU(6)
adapter; independent consumers use `ResidualGaugeTensor.lean`. See the
[shared-boundary dossier](SHARED_SELECTION_RULES.md).

## 6. Scope and limitations

### What is not yet proved

These are ordered **internal gauge** tensors, not full local fermion
operators after imposing Lorentz contraction and anticommutation. In
particular, nonzero on an ordered tensor product does not by itself prove
nonzero in a Grassmann or exterior-algebra quotient.

For an arbitrary `ContinuousWeylModel`, its torus and residual invariance
alone do not identify these standard spaces inside the radical or give
full non-Abelian mass invariance. The neutral benchmark below now carries
the additional full-group action and equivalences explicitly.
`ConcreteWeylFullMass` uses a prescribed torus eigenbasis; it is not yet
proved that the same selected mass is invariant under the natural full
gauge action. Do not infer this from its complete SM weight spectrum.

The [full-gauge mass milestone](../GUT/SM_GAUGE_MASS.md) now constructs the
decomposed 27-dimensional candidate with a nonzero mass, proves its actual
15-dimensional radical, and transports both tensors onto that radical and
its dual. `StandardSMExterior` and `StandardSMUVFields` prove the full-group
branching equivalence from actual analytic SU(6) `15 + 2 bar6`.
`StandardSMUVMass` now realizes the nonzero mass, exact SM radical, and
nonzero invariant tensors on that UV direct-product space, with neutral
residual action. `StandardSMOrdinaryMass.continuousModel` now places this
mass in the continuous interface via a proved torus/residual equivalence
and a compatible full-group extension. `StandardSMContinuousTensor` gives
both tensors on that model's actual radical, with full-gauge invariance,
witnesses equal to one, and exact restriction to its original torus action.
This is an existence construction, not a uniqueness result for the extension;
see [the branching bridge](../../inputs/GUT/SM_BRANCHING.md). Older masses and
endpoints are unchanged. No nonzero Wilson coefficient, interaction
strength, or decay amplitude is assumed.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
