# Full Actual Family: Necessary Copies and Qque Exclusion

The fixed family now includes arbitrary copies of actual 10, bar5, 40 and 50
and their algebraic duals. The standard SM covering group is the full retained
action: no additional residual symmetry acts on generations. The mass is any
symmetric complex bilinear invariant mass on the whole original field space.

The result excludes simultaneous positive-generation SM light content and
prohibition of every admitted light qque coefficient in this class. It does
not exclude SM-compatible inputs themselves. Ordinary 10 plus bar5 has the
standard generation content, as established by the existing actual branching
equivalences. Nor does a nonzero invariant coefficient establish a generated
interaction, Wilson coefficient, amplitude or proton-decay rate.

## Actual UV copy constraints

Write p_i for source counts and q_i for conjugate partner counts, in the order
10, bar5, 40, 50. An exact light target of N SM generations forces

| Representation | Necessary copy constraint |
| --- | --- |
| 10 | p_0 - q_0 = N |
| bar5 | p_1 - q_1 = N |
| 40 | p_2 = q_2 |
| 50 | p_3 = q_3 |

All counts are arbitrary natural numbers. No finite copy cutoff or selected
mass matrix is used. `ActualFullFamilyIndex.net_constraints_of_exact_sm`
proves these conditions from an actual equivariant equivalence of the mass
radical with N copies of the standard generation representation. The latter
is the actual restricted 10 plus bar5, whose full-SM branching is already
proved. A weaker actual light dual-character condition suffices for
`net_constraints`; no formal UV profile is an input.

These conditions are necessary, not sufficient. Equal conjugate counts do
not prove spectators are massive; the chosen mass may retain vectorlike
light fields. The proof does not construct an exact SM spectrum from counts.

`copy_constraint_prefilter` makes the search direction explicit: if the
counts violate any row, no invariant mass can give that exact SM target.
This exclusion can therefore be applied before choosing a mass matrix.
Passing the prefilter is not a realization certificate.

## Why the character bridge closes

[ActualHyperchargeProfiles](../../../GUT/SU5/Branching/ActualHyperchargeProfiles.lean)
uses actual Five and Ten eigenbases and the existing exterior eigenbasis trace
theorem. The symmetric-square basis gives the actual symmetric trace. The
proved exact wedge sequences give the actual 40/50 traces. Consequently:

| Actual representation | Hypercharges 6Y and dimensions |
| --- | --- |
| 10 | -4:3, 1:6, 6:1 |
| bar5 | 2:3, -3:2 |
| 40 | -9:2, -4:12, 1:18, 6:8 |
| 50 | -8:6, -3:16, 2:21, 7:6, 12:1 |

These are proved hypercharge traces, not an irreducible color/weak branching
classification. Finite coefficients are checked by Lean's kernel, not imported
from the earlier Python character check or formal profile list.

[CyclicHypercharge](../../../GUT/SU5/Branching/CyclicHypercharge.lean) restricts
to the order-31 phase subgroup. Its character-polynomial evaluator is injective,
using distinct-character linear independence. All occurring charges and their
negatives lie between -12 and 12, so these rows do not alias modulo 31.
Charge 12 isolates the net 50 count; charge -9 isolates twice the net 40 count.
Charges 6 and -3 then isolate 10 and bar5. The actual arbitrary symmetric-mass
dual-character identity transports the light target to these UV rows.

This avoids needing the entire color/weak spectator decomposition for these
necessary count constraints. It does not prove that decomposition.

## Actual light coefficient endpoint

[ActualFullFamilyQque](../../../GUT/SU5/SelectionRules/ActualFullFamilyQque.lean)
selects one generation from the exact SM light equivalence. It constructs
injective Q, uc and ec maps into the unchanged radical, and their actual
invariant ranges with full gauge-equivariant identifications. The physical
right-handed fields use the dual uc/ec ranges and the proved bidual maps.

[StandardGaugeQqueExterior](../../../Physics/StandardModel/Operators/StandardGaugeQqueExterior.lean)
uses the existing SM epsilon contraction, Weyl-spinor coefficient and
fermionic alternation. Explicit basis slots prove nonzero exterior descent;
transport gives a nonzero coefficient on the selected actual light ranges.
No field decomposition or nonzero coefficient is supplied as a premise.

`ForbidsEveryLightQque` quantifies over these actual SM species subspaces and
their exterior coefficient spaces. `no_sm_prohibiting_input` proves that no
mass in this full family has both an exact positive-generation SM radical
and that prohibition. An all-B1 prohibition covering these qque carriers
is therefore impossible under the same retained action. A selected-domain
prohibition that omits these carriers is not covered by this conclusion.

The coefficient-side obstruction is an application of known SM gauge
invariance, not new independent coverage of the existing SM-spectrum no-go.
The additional bridge is the actual arbitrary-mass UV count constraint and
its connection to actual light participating fields, without formal-profile
premises or a full spectator branching construction.

## Remaining scope

The declared gauge-only, exact-SM endpoint is complete. Additional residual
actions, alternative embeddings, other representation families and relaxed
light targets require their own input proofs. Neutral singlets are not yet
included in this concrete exact-spectrum adapter. Gauge-only qque allowance
does not rule out a vanishing generated coupling in a particular model.

SM compatibility here means the specified fermion spectrum and gauge action.
Scalar/VEV realization, Yukawa couplings, realistic fermion masses and a full
UV model construction are not certified by the light-spectrum equivalence.

Exact one-copy Q/uc counts inside 40 and its full color/weak branching remain
unproved and are not needed by this result. No universal classification of
proton protection, anomaly cancellation, matching or phenomenology is claimed.
See [verification](verification.md) for the audit and build record.
