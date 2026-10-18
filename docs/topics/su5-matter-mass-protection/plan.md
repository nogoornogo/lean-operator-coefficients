# Staged SU(5) Transfer And Matter/Mass Assessment

Implementation authorized at stage 01; branch creation separately authorized.
The bounded pass reached its proof/feasibility stop; see [results](results.md)
and [verification](verification.md). The phase descriptions below retain the
frozen plan, not a claim that every proposed generalization was proved.

## Convention Dictionary And Claim Boundary

Fix the existing standard SM cover embedding in SU(5), all-left matter
Q, u^c, e^c, and physical qque built from Q twice and the right-handed duals
of u^c and e^c. Use the existing left/right SL(2,C) spinors and fermionic
alternation. H is initially finite Abelian, acts complex-linearly and
unitarily, and acts trivially on the spinor factors. Actual species characters
must be derived from the genuine field action, not assigned to arbitrary
pointwise factors. No charge signature alone counts as the endpoint.

Do not equate a dual chiral index with the full light spectrum or infer a
light-field placement from it. Mass invariance is imposed at the broken
phase under SM and H; full-SU(5) invariance of the mass is not a default
requirement. Vacuum/coupling origin and quantum exactness are separate inputs.

## Phase A — Transfer The Scalar/Block Mechanism

Start with actual one-copy `10 + bar5` matter and the existing standard
branching. Use zero mass as the first inhabited control, consistent with
[the existing Georgi-Glashow result](../georgi-glashow-exterior/README.md).
It is not a physical claim that every SU(5) model has zero mass.

Supply a genuine unitary H action U and pointwise SU(5) matrices
`s(h) = diag(c(h) I3, w(h) I2)`, with `c(h)^3 w(h)^2 = 1`.
Require `U(h) = rho(s(h)) E(h)`, where E is scalar a on the ten and
scalar b on the bar-five. Neither s nor E is assumed homomorphic.
Do not infer a general automorphism action or classify all covariant U.

Derive on the actual ten species:

```text
Q = a c w,   u^c = a c^2,   e^c = a w^2
chi_Q^2 chi_uc^-1 chi_ec^-1 = 1.
```

Use nonzero species and U's group law to derive genuine characters.
Transport the existing named physical coefficient and its nonzero witness
to actual light species. SU(5) membership restricts admissible factors but
is not a step in the phase cancellation. Check agreement with the existing
commuting zero-mass control; distinguish what is newly proved.

Deliverables: SU(5)-owned adapter, an inhabited zero-mass control, strict
audit and a hypothesis comparison with SU(6). No SU(6) proof imports in the
new SU(5) endpoint; reusable mathematics/physics stay in their own layers.
Freeze actual Lean signatures after inspection. A new branching foundation
or a missing nonzero transport is a scope gate, not an assumed success.

## Phase B — Remove The Particular Mass Formula

Keep phase-A matter, embedding and action fixed initially. Allow a symmetric
complex-bilinear mass B invariant under the joint SM/H action. Derive radical
stability. Admit the selected species only through injective equivariant
maps into the actual radical, with the phase-A actions and nonzero domains.

The intended theorem is conditional on these light-field certificates;
arbitrary invariant B alone does not guarantee them. Separate:

1. conditions sufficient to transport the physical coefficient;
2. conditions ensuring a mass actually realizes those light species;
3. the stronger condition of an exact full SM light spectrum.

Determine by existing SM branching/bilinear pairing interfaces whether the
one-copy chiral carrier forces the admitted SM-invariant mass to vanish.
Do not advertise a nonzero mass family if that class only contains zero.
Use one bounded route: decomposition into SM sectors and allowed dual
pairings. Record either a proved characterization or the exact missing API.

If the species exhaust the relevant light carrier, use equivalences. If they
are proper subspaces, prove an equivariant projection/splitting before
claiming a coefficient on the whole light carrier. An injection alone is
insufficient to extend a functional. The narrow participating-species
endpoint remains distinct from a whole-light theorem.

Deliverables: mass-independent conditional adapter, a ledger of supplied
versus derived light conditions, and a bounded mass realizability result.
The mass characterization is a question to settle, not a theorem premise
silently inserted into the transfer proof.

## Phase C — Bounded Matter And Mixing Assessment

Use two routes, each inspected once before committing to proof signatures:

| Route | Matter change | Finite question |
| --- | --- | --- |
| C1 | `n(10 + bar5)`, n > 0 | Which copy-space actions and common surviving light submodules retain the coefficient under scalar/block compensation? |
| C2 | One chiral `10 + bar5` plus one `10 + bar10` pair | Which SM/H-invariant mass pairings and mixing preserve a common participating light placement, and where does the certificate fail? |

C1 reuses existing copy-space/centralizer results rather than assuming a
single scalar on every generation. Do not silently force a general flavor
action into the phase-A species-character interface. Either extract a common
eligible submodule with an equivariant splitting or use an existing general
physical coefficient criterion whose actual hypotheses are verified.

C2 provides the first bounded nonzero-mass candidate. Freeze allowed actions,
the mass parameter family and desired radical statement before calculations.
Do not scan arbitrary representations, arbitrary generation counts or UV
couplings. These routes do not classify all mass matrices or all light
placements; missing bridges may yield a scoped feasibility endpoint.

For each route report: actual radical/species, residual action, sufficient
condition for nonzero qque, and unresolved cases. Failure of the shared-ten
certificate is not vanishing of qque. Vanishing of qque alone is not complete
Delta-B-one protection. A protecting candidate would require a separately
scoped full physical coefficient classification.

## Stop Conditions And Later Applications

Accept a conditional theorem, a proved counterexample to a proposed
generalization, or a precise bounded feasibility decision. Stop before new
representation classification foundations, non-Abelian or antilinear actions,
arbitrary embeddings, further matter routes, or all-sector protection claims.
Changes to these boundaries require a new scope decision.

After the SU(5) conditions are settled, propose separate SU(N), Spin(10) and
E6 adapters. Group embeddings alone do not preserve invariants under extra
residual actions; each application must supply actual light fields and the
full residual-action bridge. Preserve existing E6 literature boundaries.
No matching, decay rates, RGE, hadronic inputs or numerical simulation is
part of this plan. No dependency changes or external agents are planned.

## Reuse Sources

- [SU(5) matter](../../../GUT/SU5/Representations/Matter.lean)
- [Exterior-square branching](../../../GUT/SU5/Branching/ExteriorSquare.lean)
- [Georgi-Glashow actual source](../../../GUT/SU5/SelectionRules/GeorgiGlashowSource.lean)
- [Existing physical consumer](../../../GUT/SU5/SelectionRules/GeorgiGlashowQque.lean)
- [Neutral coefficient and transport](../../../Physics/StandardModel/Operators/NeutralQqueExterior.lean)
- [SU(6) fixed-class plan](../su6-twisted-protection/generalization-plan.md)

## Verification

Planning acceptance: `node tools/docs/check-links.mjs` and
`git diff --check`. No Lean build is rerun for this documentation-only plan.
On stage 01, the link check passed (532 Markdown files, zero errors) and
the diff check passed. No branch was created, commit made or merge performed.

Implementation acceptance: focused builds of each new adapter/audit, strict
transitive audits permitting only `propext`, `Classical.choice`, `Quot.sound`,
then one serialized `lake build`; layout, local link and diff checks.
Rerun `python3 tools/qque/audit_one_generation.py` when integrating a new
physical consumer. Add reusable exact controls only for the finite mass or
mixing cases actually implemented, with conventions and scope documented.
Existing proof checkpoints are references, not verification of new adapters.
