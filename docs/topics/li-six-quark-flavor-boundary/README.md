# Printed Six-Quark Basis And Flavor Boundary

- ID: `li-six-quark-flavor-boundary`
- Status: completed
- Result type: exact printed-span and bounded physical completeness theorem
- Working branch: `proof/li-six-quark-flavor-boundary`
- Integration target: `proof/li-six-quark-basis`
- Parent exception: bounded child of the unmerged literature certificate topic;
  no integration into master is authorized.

## Frozen Endpoint

1. Prove that the span of all exchange-word orbits of the ten printed seeds
   equals the kernel of the separating probe, not merely a proper subspace.
2. Identify the missing flavor component with symmetric up inputs and four
   alternating down inputs, via the existing statistics quotient interfaces.
3. Transport its vanishing for down dimension at most three to a completeness
   equivalence for the printed contractions on the physical sector.

Keep distinct finite-dimensional complex up/down carriers, arbitrary residual
group and existing model inputs. No new pins, literature premises, full Schur
decomposition, other operator sectors or counting polynomial are included.
The tensor/exterior descent must use existing universal properties. Stop for
user judgment if a new foundational project or changed hypotheses are needed.

## Sources And Verification

- [Parent certificate](../li-six-quark-basis/README.md).
- [Existing dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md).

Acceptance requires focused build, persistent strict axiom audit, full build,
layout, literature script regression, local links and diff checks.
The [flavor-boundary dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_FLAVOR_BOUNDARY.md)
records the implemented statements. The missing component is identified by
universal-quotient descent and an exact evaluation/zero equivalence; a separate
full residual-Hom classification on that quotient is not claimed.

On stage 01:

- `lake build Physics.StandardModel.Operators.Audit.AuditLiSixQuarkFlavorBoundary`:
  3,305 jobs, 13 strict transitive axiom checks passed.
- `lake build`: 6,417 jobs, successful; no warnings or errors in the captured log.
- `python3 tools/li-six-quark-check.py`: exact 25/24/25 ranks for both Young
  composition orders and the existing inverse assertions passed.
- `node tools/layout/check-layout.mjs`: 1,090 modules, passed.
- `node tools/docs/check-links.mjs`: 410 Markdown files, zero errors.
- `git diff --check`: passed.

The three bounded deliverables are implemented: hyperplane equality and rank,
universal-quotient descent with exact probe recovery, and the physical
printed-Hom equivalence for down dimension at most three. No new foundational
project or user scope decision was necessary. No pins or audit exceptions
were changed. The persistent audit permits only `propext`, `Classical.choice`
and `Quot.sound`.

Child integration is recorded by Git ancestry against the parent target.
Master integration remains unauthorized. Full residual-Hom classification
of the quotient as a separate factor and whole-paper counting are not part
of this endpoint.
