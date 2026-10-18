# Independent Yukawa Blocks

- ID: yukawa-independent-blocks
- Status: completed
- Checkpoint detail: completed (integration recorded by Git after verification).
- Result type: generated-mass identity, independent couplings and exact spectrum.
- Working branch: `proof/yukawa-independent-blocks`.
- Integration target: `master`.

## Frozen Endpoint

Continue past the common rescaling family. Use unchanged 15 + 2 bar6 SU(6)
matter and the existing symmetric-form scalar. Extract independent allowed
couplings using the equivariant exterior-matter projector and its complement.
At the existing vacuum distinguish the heavy five and singlet pair. Prove
independence of two couplings and classify their generated radicals for all
complex coefficients, including partial rank loss. This subspace is not
asserted to exhaust the full endomorphism algebra; its irreducible decomposition
remains a separate prerequisite, not an assumed input.

Reuse orthogonal-product mass lemmas and actual branching. No new Higgs
multiplet, potential, amplitude, pins or axioms. Stop on scope-changing inputs.

## Sources And Verification

- [Previous family](../yukawa-family-spectrum/README.md)
- [UV branching](../../../GUT/SU6/SelectionRules/Models/StandardSMUVFields.lean)
- [Symmetric scalar](../../../Physics/FieldTheory/Yukawa/SymmetricScalarYukawa.lean)
- [Paired mass](../../../Physics/FieldTheory/Mass/LightInheritanceBoundary.lean)

## Construction

Let P project actual matter onto its exterior-square summand, and Q=1-P.
Both commute with full SU(6), not merely the residual group. From the
existing invariant Yukawa tensor Y0 define

```
Y5(s)(x,y) = Y0(s)(Px,Qy) + Y0(s)(Qx,Py)
Y1(s)(x,y) = Y0(s)(Qx,Qy)
Y(a,b) = a Y5 + b Y1
```

At the unchanged specified vacuum and zero bare mass, the target normal form
is zero on the 15-dimensional light representation and Dirac pairings with
coefficients a on Five + Five* and b on the singlet pair. Here Five is the
color-triplet/weak-doublet sum in the existing branching, not a new UV field.

| a | b | Light dimension | Additional light representation |
|---|---|---:|---|
| nonzero | nonzero | 15 | none |
| nonzero | zero | 17 | singlet and its dual |
| zero | nonzero | 25 | Five and its dual |
| zero | zero | 27 | both pairs |

`mass_eq` identifies the actual Yukawa-generated mass with this normal form.
Two normalized evaluations recover a and b. `coupling_eq_iff` proves that
two couplings in this family agree exactly when both coefficients agree.
`radical_finrank` and the four named strata prove the table for the generated
mass; `fullRadicalEquiv` identifies its entire radical as a representation,
not merely its dimension or a retained subspace.

## Implementation

- [Orthogonal mass and radical products](../../../Physics/FieldTheory/Mass/OrthogonalMass.lean)
- [Equivariant projected Yukawas](../../../Physics/FieldTheory/Yukawa/ProjectedYukawa.lean)
- [Branching normal form and probes](../../../GUT/SU6/Yukawa/TwoBlockSpectrum.lean)
- [Actual couplings, mass identity and spectra](../../../GUT/SU6/Yukawa/IndependentCouplings.lean)
- [Shared audit](../../../Physics/FieldTheory/Yukawa/Audit/AuditProjectedYukawa.lean)
- [Model audit](../../../GUT/SU6/Audit/AuditIndependentCouplings.lean)

Evaluation lemmas for product equivalences and mass-transport certificates
avoid repeatedly unfolding concrete analytic representations. The existing
`withResidualEquiv` now exposes the same `gaugeEquiv` linear map directly,
using the neutral-action equality only in its intertwining proof. Its
dependents are rebuilt; no representation or physical hypothesis is changed.
The existing `StandardSMUVCoordinates.withResidualEquiv_linear` statement is
unchanged; its proof is now `rfl`, with obsolete private cast helpers removed.

## Boundaries

The endpoint classifies a two-parameter family inside the allowed Yukawa
space, not the entire space. The prior Hom-space
classification still parameterizes all allowed couplings abstractly; the
dimension/basis of that full space and spectra for its other couplings are
not established here. The nonminimal symmetric-form scalar and fixed vacuum
are unchanged. Residual H acts neutrally, as in the original completion.
No potential minimization, realistic scalar selection or decay amplitude.

## UV Connection

The earlier component milestone `checkpoint 01` excluded the generated-mass identity
because its direct specialization timed out. A user-authorized diagnostic pass
isolated the failure to converting the concrete complementary branching proof
between representation-map and linear-map coercions. `transformed_complement`
instead derives that identity generically from `q x = x - p x`, linearity and
the retained projection identity. `anti_eq_sub` proves the small concrete input.
The original projector definitions, physical inputs and equality are unchanged.
`projected_mass_form` and `mass_eq` now pass without increased heartbeat limits.
See [kernel diagnosis and resolution](kernel-boundary.md) for the failed route
and the accepted replacement. No new assumption or trust exception was added.

## Verification

No web source used; proofs use the linked repository constructions and pinned
mathlib APIs. Lean LSP unavailable; source inspection and builds used instead.

- Focused `lake build Physics.FieldTheory.Yukawa.Audit.AuditProjectedYukawa
  GUT.SU6.Audit.AuditIndependentCouplings`: passed, 4244 jobs, 15 + 29 strict
  transitive axiom checks (only propext, Classical.choice, Quot.sound).
- Final `lake build`: passed, 5850 jobs, including the generated-mass endpoints.
  The earlier component milestone's first full run exposed the obsolete
  private residual-cast proof in `StandardSMUVCoordinates`; after replacing it
  with the same public linear-map equality proved by `rfl`, the full run passed.
  Existing dependency warnings remain; no new-source warnings were emitted.
- `node tools/layout/check-layout.mjs`: passed, 799 modules.
- `node tools/docs/check-links.mjs`: passed, 301 Markdown files, 1826 local
  links, 33 fragments. `git diff --check`: passed.
- No new heartbeat overrides, dependency pins, axioms or audit exceptions.
  Qque/exchange definitions were not changed; their separate computational
  regression scripts were not rerun.

Commit and no-ff merge to the recorded target after acceptance; repeat the
full build, layout, links and diff checks on the merged state. Git ancestry
records integration. Retain the topic branch and do not push.
