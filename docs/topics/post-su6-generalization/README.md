# Generalization After The SU(6) Check

- ID: post-su6-generalization
- Status: completed
- Checkpoint detail: completed (original planning checkpoint).
- Result type: documentation and source-based implementation plan.
- Working branch: `docs/post-su6-generalization`.
- Integration target: `master`.

Subsequent implementation: the user authorized starting directly with the
variable-background endpoint, retaining the fixed-background route as fallback.
The [uniform matching result](../sun-variable-tree-matching/README.md) now
proves the variable-background theorem and recovers the fixed family as a
specialization. The sequencing recommendations below are the original plan,
not outstanding prerequisites or a description of the current proof boundary.
The later [third-stage transport](../sun-conjugate-matching/README.md) implements
compatible ambient conjugation and mediator-coordinate changes, but does not
include independent dynamical mass mixing or classify inequivalent embeddings.

## Endpoint And Evidence

Update priorities after the [SU(6) check](../su6-tree-matching/README.md),
without changing Lean sources or extending the physical scope. Separate
proved reusable interfaces from proposed theorems. This planning task ends
with a bounded next implementation milestone, not automatic implementation.

SU(6) supplies actual exterior-action current support and explicit diagonal
mass compatibility, not merely an assumed nonzero exchange. It validates
the [structural inheritance API](../mediator-inheritance/README.md) on a
larger-group example. It does NOT validate the no-shared-constituent premises
of the [representation-separated API](../representation-separated-exchange/README.md).

The reusable mechanisms already exist:

- [Exterior compression](../../../Math/RepresentationTheory/ExteriorSquareCompression.lean)
  works for arbitrary dimensions and split linear inclusions.
- [Diagonal adjoint mass](../../../Math/LinearAlgebra/DiagonalAdjointMass.lean)
  gives the entrywise squared weight difference for any finite index type.
- [Exchange inheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)
  allows arbitrary spectator spaces and invertible masses.
- [Qque transfer](../../../Physics/StandardModel/Operators/QqueMediatorInheritance.lean)
  transports the generated exterior sector, not just the ordered tensor.
- The [SU(6) assembly](../../../GUT/SU6/Matching/TreeMatching.lean) still
  enumerates a fixed finite set of roots. That is the next restriction to remove.

## Priority 1: A Uniform Exterior Family

Proposed first milestone: `N = 5 + r` for arbitrary natural r, exterior-square
matter on `C^N`, and the retained first-five-coordinate ten. Use the actual
exterior-power action of the defining matrix representation and identify
the retained SM fields. Do not introduce abstract currents with assumed support.

Freeze the background to `v diag(2,2,2,-3,-3,0,...,0)` and keep nonzero real
g,v and the existing paired quadratic action convention. The proposed endpoint
is equality of the full broken-root exchange with the SU(5) exchange and
nonzero generated qque exterior sector, uniformly in r.

1. Replace the fixed inclusion/projection and root enumeration by indexed
   constructions. Derive retained currents and vanishing additional currents
   using exterior compression, not dimension-by-dimension `fin_cases` proofs.
2. Construct the `6 + 5r` broken root pairs, prove exhaustive coverage,
   derive masses `25 g^2 v^2`, `4 g^2 v^2`, `9 g^2 v^2`, and assemble the
   invertible mass on this sector. Extra-to-extra directions are massless
   for this background and must not be inverted.
3. Apply existing inheritance and qque transfer. Recover r=0 and r=1 as
   equalities with the checked SU(5)/SU(6) constructions, including current,
   mass and coefficient conventions, rather than unrelated nonzero examples.

Acceptance: a quantified family theorem, actual-action/SM-field identification,
derived support and mass identities, and the two specialization controls.
Pure finite-dimensional helpers belong in Math; qque adapters in Physics;
the specified matrix-group family in GUT. Keep existing checked files intact
until the specializations pass. No new compact-group topology is needed for
the intended algebraic endpoint; if that identification demands new foundations,
stop and report the boundary rather than silently weakening the claim.

## Priority 2: Variable Diagonal Backgrounds

After Priority 1, propose real diagonal entries
`(a,a,a,b,b,d_1,...,d_r)`, with `3a + 2b + sum d_i = 0`, `a != b`, and
nonzero real g. These entries include their scale; no separate v is necessary.
Keep the same retained matter and action convention.

Define broken channels by `i < j` and unequal diagonal entries. Construct
the mass inverse only there. Derive zero projected currents also for
extra-to-extra roots when these become massive. Allow coincidences among
the d_i or with a,b; do not require all additional directions to be massive.
The expected ordered scalar is `-g^2/(g^2 (a-b)^2) = -1/(a-b)^2`, with a
nonzero qque descent. This formula is a proposed theorem, not a checked result.

This phase removes the special vacuum parameters, not the diagonal-background
ansatz. Tests must include the old background, coincident spectator weights,
and unequal spectator weights. The case a=b is excluded because the core
is then massless; do not claim the local heavy-exchange formula there.

## Later Options And Deferrals

| Direction | Priority and gate |
| --- | --- |
| Compatible changes of basis and split embeddings | Next optional step after the family: transport action, background, currents and pairing together; arbitrary group inclusions alone are insufficient. |
| Concrete representation-separated application | Independent route when a useful auxiliary symmetry and actual separation data are available; SU(6) direct compression has not supplied these premises. |
| Mixing of equivalent mediator summands | Separate investigation, possibly via effective block masses; zero extra currents alone does not fix the retained block of the inverse mass when mixing is allowed. |
| Other matter representations, Spin or E6 | Defer until an actual action supplies the needed currents; neither exterior compression nor the SU(N) family automatically covers them. |
| Generic nonzero loci or codimension | Defer until a specified parameter-to-generated-coefficient map warrants it; not a replacement for deriving nonzero generation. |

No stage infers a selected vacuum, light mass radical, anomaly-free matter
content, full UV action, physical amplitude or decay width. The selection-rule
theorem alone still does not imply generation. The gain sought is uniform
derivation of the matching inputs, not a renamed nonzero premise.

## Execution And Verification

Recommend implementing Priority 1 only as the next bounded topic. Freeze its
statement and create its proof branch from the then-current integration target
when authorized; future proof branch/base are unassigned in this document.
Permitted routes are exterior compression and diagonal-mass algebra followed
by existing inheritance. Stop after the family and specialization controls;
Priority 2 is a separate checkpoint, not an automatic scope expansion.

Future proof acceptance requires focused/full builds, persistent strict
transitive axiom audits, existing exact qque regressions, and layout/link/diff
checks. No new axioms, `sorry`, dependency changes or weakened audits.
For this documentation-only update, run local link and diff checks before
and after integration. No Lean build or computational regression is rerun;
the previous SU(6) verification is historical evidence, not a new baseline.

Documentation checks: `node tools/docs/check-links.mjs` passed (291 Markdown
files, 1718 local links, 33 heading fragments); `git diff --check` passed.
Commit and merge this documentation branch with `--no-ff`, repeat these
checks, retain the branch and do not push. Git ancestry records integration.
