# Extended Certificate: Results And Verification

## Verified Endpoint

`LiSixQuarkConvention.candidate_coordinates` identifies each normalized signed
Young sum of literal epsilon contractions with its independently measured
five-color by five-Weyl array. `LiSixQuarkOrbitData.step_checked` checks each
one-step exchange exactly; `orbit_column` composes those checks into the selected
25 columns. Both products of the rational basis matrix and inverse are checked.

`LiSixQuarkLocalBasis.orbit_independent`, `literal_reconstruction` and
`local_finrank` establish a literal basis of the independent local invariant
space, not an image-defined substitute. `extra_outside_printed_span` proves
that no word in the four exchange generators applied to the ten printed seeds
can supply the additional component. Exact rank 24 of that span is a Python
regression result here, not a separately stated Lean dimension theorem.

`LiSixQuarkResidual.literal_local_assembly` assembles the actual contractions
at each flavor input. `statistics_iff` retains all typed exchange constraints.
`physicalEquiv` and its two inverse identities transfer completeness to the
existing normalized exterior sector, and `onFieldsEquiv` uses supplied actual
field identifications. Scalar specialization agrees with the old physical
two-probe equivalence and has dimension two.

`LiSixQuarkFourFlavor.physical_nonzero` supplies an explicit physical witness
with trivial residual symmetry, up carrier C and down carrier C^4. Its down
flavor determinant restores Fermi alternation to the added local line.
`separating_probe_witness` evaluates to one on that input. The extra component
is not a third scalar-flavor operator.

## Acceptance Checks

From the repository root, with the pinned Lean/Lake toolchain on PATH:

```sh
lake build Physics.StandardModel.Operators.Audit.AuditLiSixQuarkBasis
lake build
python3 tools/li-six-quark-check.py
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Focused build: 3,295 jobs and 18 strict transitive axiom checks passed. Full
build: 6,412 jobs, successful. The new source checks have no residual warnings.
The exact Python checks cover both Young composition conventions, the 25/24/25
rank controls, and both proposed inverse products. Lean independently checks
the implemented row-column certificate; no external rank theorem is assumed.
Layout checks cover 1,085 modules. Link and whitespace checks pass.

## Retained Boundaries

The [dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md) and
[source dictionary](source-recovery.md) fix the interpretation. The added seed
is explicitly an extension, not a recovered eleventh printed entry. No full
eleven-factor Schur decomposition, unrestricted flavor coordinates, universal
dimension-two claim, four-component C normalization, hook-length projector
scale, software-wide discrepancy, or whole-SMEFT completeness is inferred.
The Lean and dependency pins are unchanged. Master integration remains subject
to explicit user instruction.
