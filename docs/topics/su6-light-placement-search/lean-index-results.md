# Lean Certificate for the Five Index Obstructions

This records the original certificate implementation. The later
[structural row derivation](../proof-readability-review/finite-index-replacement.md)
replaces its closed certificate checks while preserving the supplied inputs
and nonexistence statements.

The [frozen certificate plan](lean-index-plan.md) is complete. The
[Lean source](../../../GUT/SU6/SelectionRules/Models/FiniteIndexCertificate.lean)
now proves that no rational coefficients solve the necessary charge-index
system for any of the five normalized Z5 light targets. This replaces reliance
on Python elimination for the algebraic inconsistency itself.

## Explicit data and certificate

`branching` records complete SM profile lists for the seven formal characters
1,6,15,20,21,35,70. Multiplicities are repeated list entries. `rows` selects
seven charge/species index rows, and `column` computes each profile's
positive multiplicity minus its conjugate at opposite Z5 charge. `lightProfile`
records the complete Q,U,D,L,E target for each normalized representative.
`target_dictionary` proves that the separating target rows are exactly the
index of that supplied light profile.

Each certificate uses at most three nonzero integer weights on these rows.
`annihilates` checks all seven representation profiles at all five charges;
`separates` checks that its target pairing is one. These finite identities
are proved with kernel `decide +kernel`, not native_decide or an external
oracle. The failed initial tactic expansion was replaced with this kernel
computation; no heartbeat allowance or axiom exception was added.

`no_solution` uses finite sum distributivity and those two identities:
if the target were any linear combination of columns, its certificate value
would be zero, contradicting one. It covers arbitrary rational coefficients,
so in particular signed integer and nonnegative integer multiplicities.
`no_integer_solution` states the signed-integer case explicitly. Conjugate
profiles contribute negative original columns at opposite charges, already
included in the rational relaxation.

`Admitted` exposes the necessary matrix-index transport as an application
predicate; `not_admitted` proves its impossibility for every target. This
predicate is not an independently proved constructor for an actual SU(6)
model and is not named a physical model-existence equivalence.

## What is now strict and what remains conditional

| Statement | Status |
| --- | --- |
| Finite profile/target matrix inconsistency for all five representatives | Lean-proved, arbitrary rational coefficients |
| Target rows coincide with the explicitly recorded light profile | Lean-proved |
| Static branch data agree with prior complete-character computation | Reproducible independent script check |
| These profiles are actual continuous SU(6)-to-SM branching equivalences | Not newly proved here |
| A given invariant mass/actual radical necessarily transports to this matrix | Application admission condition; not proved for a newly constructed UV model |
| No arbitrary SU(6) protecting model exists | Not asserted |

Thus any physical construction that supplies the stated profile/index
transport is excluded rigorously. Completing a source-level SU(6) theorem
without that bridge as a premise would require actual branching equivalences
for the newly introduced 20,21,35,70 and mass-index preservation on their
radicals. No UV character is silently substituted for actual-light evidence.
That is a distinct foundational deliverable, not discharged by the certificate.

## Reproducibility and endpoint

[The static-data checker](../../../tools/su6-light-placement-search/check_lean_index_data.py)
compares every explicit branching list to the complete-character computation,
checks target charges, and independently checks all 175 annihilation and five
separation identities. This is supplemental evidence, not a Lean premise.
The proof source and persistent strict audit are registered in GUT.lean.
No mass, vacuum, anomaly, physical rate, dependency pin, merge or push was
introduced. The finite obstruction endpoint is reached; the exact scope of
further physical admission work remains visible.

## Subsequent actual-mass connection

The [actual radical-index result](physical-index-results.md) independently
excludes these targets for arbitrary actual unitary SU(6) times commuting
residual actions on the standard embedding. It derives the obstruction
from the actual mass radical via the standard SU(5) chain, without using
the finite matrix admission premise. The individual branching equivalences
remain separate; noncommuting residual actions are not covered.
