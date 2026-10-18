# Standard-Placement Scalar/Block qque Obstruction

## Result And Scope

Status: completed conditional proof phase on `proof/su6-twisted-protection`.
Further parent-topic exploration was stopped at stage 01; see
[closure and scope](closure.md). No master integration was performed during
this proof phase; subsequent integration has its own
[verification record](integration-verification.md).

The [authorized plan](generalization-plan.md) has a conditional Lean endpoint:
`GUT.ScalarBlockQque.exists_actual_exterior`. Every input in its fixed class
admits a nonzero qque exterior coefficient on participating actual light fields,
invariant under `(SM_cover × H) × SL(2,C)`.

Thus this residual action cannot prohibit every dimension-six Delta-B-one
coefficient. This is not an SU(6)-wide no-go, a generated Wilson coefficient,
a proton decay calculation or a protecting model. This phase makes no change
to the selected light placement or action class; broader exploration is deferred.

## Admission Conditions

[Input](../../../GUT/SU6/SelectionRules/Models/ScalarBlockQque.lean) fixes:

- A finite Abelian H and a genuine complex-linear representation U on the
  existing analytic `15 + bar6 + bar6` carrier.
- Unitarity through preservation of `uvInner`, the sum of the three supplied
  Hermitian forms. The product carrier's sup norm is not used as a Hilbert norm.
- Pointwise functions `a,b,d,c,w,t : H → Circle`, an actual SU(6) lift s,
  and its matrix formula `diag(c I3,w I2,t)`.
- `U(h) = rho(s(h)) E(h)`, where E is scalar a/b/d on the three respective
  summands. Neither s nor E is assumed to obey a group law. SU(6) membership
  and the matrix formula encode `c^3 w^2 t = 1`.
- Invariance of the existing exact `StandardSMUVMass.mass Unit`, through the
  named evaluation `benchmarkForm`. This is a supplied premise, not inferred
  from a positive index or from a computational mass matrix.

The standard SM embedding and branching dictionary are fixed by source, rather
than quantified over arbitrary embeddings. Neutral external scalar action uses
matrix conjugation by s; `diagonal_fixed` proves fixedness of every diagonal
matrix, including the chosen `diag(1,1,1,1,1,-5)` adjoint VEV. This does not
assert complete breaking to precisely SM or a UV origin for the mass couplings.
No topology on H is used in this algebraic result; the intended finite residual
interpretation uses discrete H. Residual H acts trivially on the chosen Weyl
spinors through the fixed external-product construction; this is not derived
from the UV matter action.

`pointwise_covariance` proves full-UV covariance by conjugation with s(h).
It does not construct a homomorphism `H → Aut(SU(6))` or an inhabitant of the
broader covariant-model interface. Such additional model data are unnecessary
for this obstruction: any model supplying the displayed inputs is covered.

Finiteness, unitarity and mass invariance remain admission conditions.
The cancellation proof only needs the displayed genuine matter action and
branching; `radical_stable` separately uses mass invariance to preserve all
actual zero modes. No premise has been replaced by an axiom or audit allowance.

## Actual Fields And Proof

The [diagonal-action adapter](../../../GUT/SU6/Adapters/StandardScalarBlock.lean)
computes the action on the algebraic exterior square and transfers it to the
actual analytic fifteen. Its first-summand embedding is injective. The existing
mass and branching equivalences prove that the following images are actual
members of the benchmark radical:

| Participating all-left field | Source in the fifteen | Pointwise U phase |
| --- | --- | --- |
| Q | color/weak tensor block | a c w |
| u^c | color/color dual block | a c² |
| e^c | weak/weak dual block | a w² |

`QuarkSpace`, `UpSpace` and `ElectronSpace` are ranges of the corresponding
linear embeddings into the original UV carrier, not substitute field copies.
Their coordinate maps are invertible. The `_gauge_restriction` and
`_residual_action` theorems identify their transported actions with the actual
restricted UV SM action and U, respectively. Their `_light` theorems establish
membership in the actual mass radical.

[ScalarEigencharacter](../../../Math/RepresentationTheory/ScalarEigencharacter.lean)
derives genuine species characters from U's group law and the nonzero embedded
species. It never asserts that the individual functions a,c,w are characters.
For the right-handed duals of u^c and e^c the phases are inverse, so

```text
(a c w)^2 (a c²)^-1 (a w²)^-1 = 1
```

holds pointwise for every h. The helper `charges` fills unused d/L entries
with zero solely to reuse the qque interface; it does not identify their
physical residual charges or establish a duql result.

[NeutralQqueExterior](../../../Physics/StandardModel/Operators/NeutralQqueExterior.lean)
combines the neutral internal qque contraction with the explicit left/right
SL(2,C) epsilon pairings, and performs fermionic alternation. Its selected
four-field witness evaluates to **2**, proving nonvanishing, rather than just
charge neutrality or an ordered internal tensor. This is the unit-flavor
normalization; the earlier symmetrized residual construction has value 4.

Species equivalences, dual/bidual equivalences and spinor extensions transport
this named coefficient to

```text
(Q_actual ⊗ S_L) ⊕ ((u^c_actual)^dual ⊗ S_R)
                     ⊕ ((e^c_actual)^dual ⊗ S_R).
```

Invertibility of the exterior transport preserves nonvanishing. These three
participating species form the coefficient carrier; no identification with an
untyped exterior power of the whole all-left radical is made. The explicit
SL(2,C) convention and functional-versus-interaction boundary remain those of
the [physical dossier](../../proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md).

## Relation To The Tested Candidates

At their named generators, the preceding finite calculations use:

| Candidate | a | b | d | c | w | t |
| --- | --- | --- | --- | --- | --- | --- |
| [C4](block-phase-result.md) | i | i | -i | 1 | -1 | 1 |
| [Nonliftable UV C2](nonlift-result.md) | 1 | i | i | i | -i | -i |

Their surviving qque phases are instances of the same algebraic cancellation.
The new theorem ranges over arbitrary finite Abelian H and pointwise factors,
including nonhomomorphic lifts, subject to the fixed admission conditions.

Neither computational candidate has been instantiated as a Lean `Input` in
this phase. In particular, a component mass matrix with its own normalization
is not a proof of invariance of the transported Lean bilinear form. Their exact
scripts remain independent checks, not theorem premises or full model certificates.
The UV C2 nonliftability proof retains its computational scope; no general lift
classification follows from this theorem.

## Verification And Remaining Boundary

Final verification at stage 01:

- `lake build Math.RepresentationTheory.Audit.AuditScalarEigencharacter
  Physics.StandardModel.Operators.Audit.AuditNeutralQqueExterior
  GUT.SU6.SelectionRules.Audit.AuditScalarBlockQque`: passed, 4,073 jobs.
  Strict transitive audits cover 11 mathematical, 9 physical and 77
  model/adapter declarations. Only `propext`, `Classical.choice` and
  `Quot.sound` are permitted; no exception was added.
- Serialized `lake build`: passed, 6,591 jobs, no warnings.
- `node tools/layout/check-layout.mjs`: 1,264 modules passed.
- `node tools/docs/check-links.mjs`: 525 Markdown files, zero errors.
- `git diff --check`: passed; statement, actual-field bridge and scope reviewed.
- `python3 tools/su6-twisted-protection/audit_nonlift.py`: six tests passed.
- `python3 tools/su6-twisted-protection/audit_block_phase.py`: six tests passed.
- `python3 tools/qque/audit_one_generation.py`: four tests passed.

The generic first-summand lemmas keep the composed analytic equivalences
abstract during kernel checking; direct coordinate unfolding had timed out.
The accepted SU(6) adapter uses the default heartbeat and recursion limits.
Dependency pins and existing checked proofs are unchanged.

Outside this class remain copy mixing, other light placements or masses,
outer/antilinear actions, non-Abelian residual actions and general flavor actions.
Quantum exactness, anomaly cancellation, all scalar sectors and matching/rates
are not supplied. No broader search or foundational project was started.
