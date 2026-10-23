# Generalization Contract And Implementation Plan

## Objective

Construct reusable, proof-producing connections from supplied algebraic model
data to existing operator-coefficient inputs. A successful consumer proves
which fields are selected, how all declared symmetry factors act, and which
interaction/relation conditions are transported. The common layer must
replace repeated connection proofs in different models; introducing a record
whose only substantive field is the desired final equivalence is insufficient.

The same field dictionary should feed the nonderivative coefficient input,
the selected derivative/EOM/IBP input and, where already supported, the
local-polynomial density helper. These routes retain their own hypotheses
and coefficient domains. No forced replacement of the public APIs is planned.

## Frozen Domain And Assumptions

- Finitely many named species with finite-dimensional complex internal
  carriers, supplied multiplicity spaces and explicit Bose/Fermi statistics.
  State the actual representation attached to each declared quantum number.
- Use the existing four-dimensional Weyl/Lorentz representations. Internal
  duality, complex conjugation and reversal of Weyl chirality are distinct
  operations, connected only by proved maps in the stated convention.
  Preserve the local-polynomial convention of independent formal conjugate
  components; it is not a new analytic reality condition.
- The core takes an actual representation of a supplied group and supplied
  restriction homomorphisms. Do not impose commutativity of the group or
  global UV/residual commutation. A product action on retained fields must be
  supplied or derived before an input requiring that product is constructed.
- A selected algebraic subspace is stable under the declared retained action.
  Boundary amplitudes and finite mass radicals have separate constructors.
  Sharing their operation surface does not identify their physical mechanisms.
- Supply invariant interaction tensors and, for vacuum evaluation, a vector
  fixed by the retained subgroup. Density-to-Euler transport uses the existing
  compatible constant linear field/direction actions and statistics conditions.
- No universal compactness, semisimplicity or unitary hypothesis is added to
  the abstract kernel/transport results. If a particular constructor needs one,
  place it in that constructor and document its use.

The finite endpoint concerns algebraic fields and coefficients. It excludes
five-dimensional boundary-value solutions, complete mixed KK spectra, scalar
potential minimization, quantum anomaly cancellation, RGE, hadronic inputs,
numerical phenomenology and experimental-fit claims. Arbitrary antiunitary
symmetry foundations, all embedding classifications and automatic branching
algorithms are not prerequisites for this topic.

## Mathematical Output

### Exact selected-field correspondence

For a supplied retained-group representation on U, construct a stable selected
subspace S. If the model starts with a larger UV group, first restrict along
the declared homomorphism; S need not be stable under the full UV group.
Given a target representation on W, provide an inverse-map criterion for an actual
equivariant equivalence between W and S. Both directions of the inverse law
are required; an injection into U or a matching character/index is insufficient.

A model-facing constructor may take linear maps e:W→U and p:U→W, with:

1. e intertwines the declared actions and its image lies in S;
2. p(e(w))=w for every w;
3. e(p(s))=s for every s in S.

Derive the selected equivalence and the extraction map's equivariance on S.
Do not require p to be an equivariant projection on all of U when only its
restriction to S is used. State the necessary-and-sufficient inverse criterion
on W and S themselves; the ambient-retraction factory is a constructive
sufficient interface, not a claimed canonical projector for every model.

### Selection factories

Reuse invariant symmetric-mass radicals and equivariant Dirac kernels.
Generalize the boundary constructor to common linear constraints/fixed spaces
with explicitly proved stability. Arbitrary intersections do not require the
different selectors to commute. Retain commutation exactly where it justifies
identifying a product projector's image with the common selected space.

Provide subgroup restriction and field-coordinate transport compatible with
these factories. Demonstrate that an exact selected identification, rather
than only a chiral index or dimension count, is preserved.

### Interaction and coefficient connections

Generalize dual pairings, invariant multilinear contractions and their
restriction along the selected maps. Respect the existing exterior/symmetric
statistics quotients. Vacuum evaluation must retain its fixed-vector premise;
prove the resulting residual invariance using the actual action.

Connect the resulting field data to existing coefficient transports and
selection criteria. Prove extraction/reconstruction and evaluation agreement
for the named consumers, not just existence of a package with matching labels.

For derivative sources, state the compatible direction action, field
substitution and full-relation transport obligations. A selected input retains
the exact preimage of relations from the full source. Do not infer that a
coefficient on a selected source extends globally, or that setting heavy
fields to zero gives the full interacting light EOM. Generate EOM from the
total density before selection; keep cancellations between terms.

## Work Stages And Provisional Effort

The table retains the planning estimates as human-effort comparisons, not
elapsed-time forecasts for autonomous execution. All five stages now have
implemented artifacts; [results](results.md) and [verification](verification.md)
record their acceptance. The estimates were based on initial source inspection
and are not measurements of the completed implementation.

| Stage | Required artifact and acceptance | Estimate |
| --- | --- | --- |
| Field description | Minimal species/representation/chirality/conjugate interface, with a written inventory of existing caller obligations | 2–4 person-days |
| Selection and exactness | Stable-subspace/constraint factories, two-sided field correspondence and transported actions; complete instances for the two selection mechanisms | 3–5 person-days |
| Interaction symmetry | Shared pairing/multilinear/vacuum restriction results and concrete invariant/nonzero controls | 4–7 person-days |
| Existing-input adapters | Additive nonderivative and full-relation derivative/density connections, with evaluation and recovery lemmas | 3–6 person-days |
| Validation and guidance | Named-model and artificial controls, strict audits, builds, usage guide, assumptions and source reconciliation | 3–6 person-days |

The provisional total remains approximately 15–30 person-days. New branching
proofs, unanticipated conjugation conventions or a missing relation-transport
theorem are the principal uncertainties. A new analytic spectral foundation is
outside this estimate. Existing mathematical cores can be reused; each model
still owes the particular selection and action evidence it needs.

## Ownership And Compatibility

- Math owns abstract stable selections, representation/inverse-map criteria,
  tensor/statistics transports and relation-quotient lemmas.
- Physics owns Weyl/chirality conventions, invariant mass/vacuum constructors
  and reusable adapters into physical coefficient/density inputs.
- GUT keeps the concrete SU(6) embedding, exterior-field maps, boundary choices
  and its instance of the shared API.

Proposed sources are placed by subject only when implemented; no speculative
empty source directories are created. Subject namespaces remain stable when
files are subdivided. Prefer additive constructors and recovery theorems over
renaming or replacing published interfaces. Existing model proofs serve as
regressions; shorten only the connection work actually covered by the new API.

## Completion And Stop Conditions

Complete the implementation endpoint when:

- The shared results are proved structurally, and both named selection
  mechanisms use them with constructed maps and exactness proofs.
- Gauge/residual actions and Weyl conventions are connected in the same
  declared field dictionary; interaction invariance and coefficient evaluation
  are preserved on the stated domains.
- A checked local-density consumer exercises full-relation transport and the
  existing density-to-Euler route under its real assumptions.
- The [validation matrix](validation-plan.md) is discharged or a source
  comparison is explicitly narrowed with all independent checks completed.
- The before/after caller inventory demonstrates reuse and identifies which
  model-specific premises are proved, retained or newly exposed. Do not trade
  a shorter proof for a stronger unproved target premise.
- Focused checks, strict transitive audits, aggregate builds, compatibility
  controls and repository documentation checks pass, and coherent milestones
  are committed on this branch.

A counterexample to a proposed universal implication is a valid scoped result.
Record it, revise that implication explicitly and continue independent checks.
A source disagreement stops only that comparison. If the endpoint requires a
new group/analytic foundation or a stronger unproved spectrum hypothesis,
record the missing interface and request a scope decision before expanding;
do not silently insert the desired light-field equivalence as a premise.

Use existing dependency pins, default proof limits, `-j2`, one compiler at a
time, 16 GiB address space, disabled core dumps and a 540-second limit per
command. No `sorry`, custom axiom, audit exception, main numerical/exhaustive
proof or large family of repeated component expansions is permitted.
