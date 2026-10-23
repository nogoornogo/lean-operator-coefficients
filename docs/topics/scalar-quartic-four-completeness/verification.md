# Verification And Sources

## Starting evidence

The recorded parent integration passed a 7753-job full build, fresh strict
re-elaboration of fourteen existing audit sources, four exact scalar
diagnostics, layout and documentation gates. This is the predecessor's
baseline, not verification of the new endpoint.

## Source roles

The pinned [predecessor source register](../scalar-derivative-completeness/references.md)
and [bibliography](../../proof/RELATED_LITERATURE.md) remain applicable.
C2 is Henning et al. 1706.08520v1 Eq. (6.3); the comparison is native Lorentz
algebra and does not prove its Euclidean group bridge. Cao et al.
2105.12742v3 Eqs. (3.28)-(3.29) supplies the density normalization. No count,
conformal-primary or renormalization theorem is assumed from either source.
New claims must be supported by Lean and audited before registration.

## Upper-bound checkpoint

All Lean checks retain two threads, cores 0,1, a 16 GiB address-space guard,
default heartbeat/kernel limits and the planned 180/540-second ceilings.

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.Algebra.Audit.AuditScalarQuarticFour \
  Physics.FieldTheory.Jets.Audit.AuditScalarQuarticFour
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
python3 tools/derivative-literature/check-scalar-group.py
python3 tools/derivative-literature/check-scalar-waves.py
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py --pending-topic scalar-quartic-four-completeness
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

The focused audit build passes 3334 jobs. Its strict inventories check 308
new namespace declarations transitively: Math source decomposition 10,
polarization 18, Lorentz tensors 170, actual quartic tensors 69, complete
source coverage 13 and coefficient upper bound 28. Only propext,
Classical.choice and Quot.sound are allowed; source-layer audits also pass.
The full build passes 7773 jobs. Both retained exact diagnostics pass
unchanged. Layout passes 2278 modules; active-topic navigation, metadata,
local links and whitespace checks pass. No new tactic/linter warning remains;
the inherited mathlib module-system import advisories remain.

During development, one monolithic generated file reached the focused
wall-clock guard. Splitting sparse rows and component reconstruction into
bounded modules resolves it. An unstructured disjunction/large tensor
constructor also reached default heartbeat limits; explicit bounded cases
and separate linearity lemmas resolve those without changing limits.
The invariant coefficient upper bound is proved on the actual whole grade.
No normalized invariant coefficient, full equivalence or new dependency pin
is claimed at this checkpoint. The construction phase below closes that gap.

## Complete endpoint

The displayed Gaussian-integer data pass conservation and nullness in Lean.
The five moment modules each prove 256 components by `decide +kernel`;
all 1280 are checked without a native-evaluation axiom. Each module was
built separately under the same 180-second guard. Their observed build
times are 67,74,64,76,74 seconds; these are measured warm-dependency runs,
not a clean-cache or universal resource estimate. The actual Lorentz metric,
wave-to-word and normalized coefficient/consumer files pass their focused
builds under the original limits.

```sh
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.Algebra.ScalarFourWaveCubature.Moments0
# Repeat the same guarded command for Moments1 through Moments4.
taskset -c 0,1 timeout 180 python3 /tmp/linear-eom-bounded.py lake build \
  Math.Algebra.Audit.AuditScalarQuarticFour \
  Physics.FieldTheory.Jets.Audit.AuditScalarQuarticFour
taskset -c 0,1 timeout 540 python3 /tmp/linear-eom-bounded.py lake build
```

The final focused audit build passes 3347 jobs; the full build passes 7785.
The two persistent strict audits cover 450 declarations transitively:

| Namespace | Strict declaration checks |
| --- | ---: |
| Math.ScalarDegreeFour | 10 |
| Math.FourWavePolarization | 18 |
| Math.ScalarFourWaveCubature | 52 |
| GUT.LorentzRankFour | 199 |
| GUT.ScalarQuarticFourTensors | 69 |
| GUT.ScalarQuarticFourSource | 13 |
| GUT.ScalarQuarticFourUpper | 28 |
| GUT.ScalarQuarticFourWaves | 10 |
| GUT.ScalarQuarticFourCompleteness | 33 |
| GUT.ScalarQuarticFourChecks | 18 |

Only propext, Classical.choice and Quot.sound are allowed. Import-layer
audits pass. There is no sorry, custom axiom, native reduction allowance,
new theorem premise or pin change. The accepted new proofs have no tactic
or linter warning. Existing-style mathlib module-system advisories remain,
including the new Gaussian-integer import.

All five exact diagnostics pass:

```sh
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
python3 tools/derivative-literature/check-scalar-group.py
python3 tools/derivative-literature/check-scalar-waves.py
python3 tools/derivative-literature/check-scalar-cubature.py
```

The new independent integer-arithmetic diagnostic reads the displayed Lean
data. It checks 144 conservation identities, 144 null identities, 1280
moment identities and K-squared normalization. Omitting one configuration
preserves the individual wave hypotheses but is detected by the moment
control. These diagnostics are not theorem premises. The three generators
reproduce all checked source bytes exactly:

```sh
python3 tools/derivative-literature/generate-rank-four-control.py
python3 tools/derivative-literature/generate-quartic-source.py
python3 tools/derivative-literature/generate-scalar-cubature.py
```

The source generation uses only the Python standard library. Its sparse
elimination, allocation and signed-permutation/Hadamard construction are
search machinery; Lean checks the resulting identities directly. This is
not integration over the Lorentz group. The raw functional's full relation
annihilation and its grade-scoped arbitrary-group invariance are separately
proved. Checked consumers cover original input restriction, selected
quotient extraction, A/B/C/Cao normalization and the anisotropic class
outside the candidate image. The input-guide examples also elaborate.

The pinned C2 primary PDF text was rechecked at Eq. (6.3), PDF p. 58, and
the K-squared representative on PDF p. 59. Its order-four coefficient agrees
with the native result. No visual PDF inspection, full-series theorem,
Euclidean/Lorentz bridge or conformal/amplitude result is claimed. The
bibliography, coverage ledger, dossier and assumptions are reconciled.

Layout passes 2289 modules, including all new source/audit aggregates.
Default topic navigation, metadata, local-link and whitespace gates pass.
The completed child remains unmerged into its parent, with no master or
remote update from this successor. The predecessor's verified parent merge
is recorded separately. Completion closes the frozen coefficient endpoint.

## Literature validation gate

The [additional comparison contract](literature-validation-plan.md) is
executed on the same unmerged branch. The primary PDF text is reinspected
for all three sources at the locations in the
[comparison report](literature-validation.md#sources-and-convention-dictionary),
including Cao's Eq. (A.20) and distinct-term permutation convention.
Screenshot retrieval returned a cache miss, so the source inspection claim
is textual. The local endpoints do not terminate the remaining paper queue.

The new `ScalarQuarticLiteratureChecks` source and its strict audit pass a
focused `lake build Physics.FieldTheory.Jets.Audit.AuditScalarQuarticLiterature`
under the same guarded command as above (3922 jobs). Eight audit files are
then freshly elaborated with the existing guarded `lake env lean -j2`
command, each under 180 seconds:

| Audit source | Strict transitive declaration checks |
| --- | ---: |
| Math/Algebra/Audit/AuditScalarQuarticFour.lean | 80 |
| Physics/FieldTheory/Jets/Audit/AuditScalarQuarticFour.lean | 370 |
| Physics/FieldTheory/Jets/Audit/AuditScalarQuarticLiterature.lean | 34 |
| Math/RepresentationTheory/Audit/AuditScalarTwoSpeciesCompleteness.lean | 159 |
| Math/Algebra/Audit/AuditScalarCompletenessHelpers.lean | 45 |
| Physics/FieldTheory/Jets/Audit/AuditScalarCompleteness.lean | 123 |
| Math/RepresentationTheory/Audit/AuditScalarCompletenessChecks.lean | 18 |
| Physics/FieldTheory/Jets/Audit/AuditScalarCompletenessChecks.lean | 31 |

All 860 inventory entries pass. Only propext, Classical.choice and Quot.sound
are allowed, and the audits retain the source-layer restrictions. The new
consumers test paper densities on the entire selected input, their inverse
coordinate, unique admitted value triples and rejection of independent
density values. No global invariant extension is presumed.

The serialized guarded full `lake build` passes 7787 jobs. All five retained
exact diagnostics listed above pass unchanged. In particular, the direct
polynomial diagnostic rechecks the paper's literal permutation expressions
in eight configurations and the nullness/conservation-removal controls;
the cubature diagnostic checks all 1280 moments and normalization. C1's
existing bounded count diagnostic also passes as a regression, without a
new C1 source-inspection claim. No new warning arises from the new proofs;
inherited module-system import advisories remain. No proof option, public
input, dependency pin or audit allowance changes.

The final layout gate passes 2291 modules. Topic navigation passes all 163
topics and outcomes; portable metadata, local links and whitespace checks
pass. The bibliography, assumptions, dossier and concise coverage ledger
link the new source dictionary and complete coefficient consumers. The
verified extension remains on the existing child branch, unmerged.
