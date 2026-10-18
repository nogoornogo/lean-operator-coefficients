# Verification

Branch `proof/sm-rank-certificates`; base `checkpoint 01`; parent/integration target
`proof/llhh-kernel-rank`. No merge or push performed.

    python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check Math/LinearAlgebra/ExactRankCertificateExamples.lean
    lake build Math.LinearAlgebra.Audit.AuditExactRankCertificates Physics.StandardModel.Operators.Audit.AuditSMRankCertificates
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Regeneration matched the committed examples. Focused builds passed (4143
jobs), including 12 Math and four Physics transitive axiom checks with only
`propext`, `Classical.choice`, `Quot.sound`, and import-layer checks. All five
generated rank results were kernel checked. Layout passed for 1550 modules.
Serialized full build passed (6893 jobs); no warning/error lines in
`/tmp/sm-rank-certificates-build.log`. Link checks passed: 825 Markdown files,
5063 local links, 94 fragments, zero errors. `git diff --check` passed.

A dependent rewrite in rank transport hit the default heartbeat limit;
composing arithmetic equalities directly resolved it. No resource limits,
dependency pins, axiom allowlists or physical assumptions were changed.

## Numerical continuation after checkpoint 02

    lake build Physics.StandardModel.Operators.Audit.AuditSMNumericalRanks
    lake env lean tools/exact-rank/constant-content-table.lean | cmp - tools/exact-rank/constant-content-ranks.csv
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Focused build passed (4142 jobs), including 11 new strict transitive axiom
checks. The CSV regeneration matched all 19268 rows. The classifier's
`evaluate_sound` theorem applies to every successful result, not only the
exported rows. Full build passed (6896 jobs), with no warning/error lines in
`/tmp/sm-constant-ranks-build.log`. Layout passed for 1553 modules; links passed
for 826 Markdown files, 5070 local links and 94 fragments. Diff check passed.
Dependent substitutions in the first classifier proof hit the default
heartbeat limit; isolating the actual rank in a definition and using proved
branch lemmas resolved it without increasing resource limits. The parity
proof similarly reuses the generic scalar-invariant vanishing theorem.

## Neutral-row literature assessment

Documentation-only follow-up: read the cited mathematical and physics sources,
checked the CSV's unknown-row split (48 Q, 48 conjugate Q, 5 L, 6 conjugate L),
and inspected the existing exterior-character and low-rank representation APIs.
Recorded two proposed routes and corrected the distinction between the neutral
constant-content prerequisite and the later mixed-content prerequisite.
`node tools/docs/check-links.mjs` passed (827 Markdown files, 5072 local links,
94 fragments, zero errors); `git diff --check` passed. No Lean source or CSV
changed, no Lean build was rerun, and no new numerical ranks are claimed.

## Structural endpoint clarification

Updated the proposed plan to reflect the user's preference for a proof uniform
in the degrees. Fixed-degree L certificates are provisional milestones, not
the final endpoint. The final proof must provide a structural multiplicity
formula and support criterion with the actual-group connection; exhaustive
numerical case checking is not a replacement. Documentation only; no Lean
source or CSV changed and no Lean build was rerun. Local link and diff checks
passed.

## Structural character milestone

Executed:

    lake build TauCeti.RepresentationTheory.SU2.Weyl.Integration
    lake build Math.RepresentationTheory.Audit.AuditStructuralCharacters Physics.StandardModel.Operators.Audit.AuditSMSourceCharacter
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

The pinned SU2 dependency built successfully (3601 jobs). Focused builds
passed (4134 jobs), including eight Math and eight Physics strict transitive
axiom checks and import-layer checks. Only `propext`, `Classical.choice` and
`Quot.sound` were admitted. Full build passed (6917 jobs), with no warnings
or errors in `/tmp/sm-structural-characters-build.log`. Layout passed for
1558 modules; links passed for 828 Markdown files, 5080 local links and
94 fragments. The initial link-check attempt encountered sandbox `git`
subprocess EPERM; the unchanged read-only checker passed on an approved retry.
Diff check passed. No CSV changes or new rank values are part of this result.

Dependent rewriting in the concrete character proof was replaced by a
separate polynomial identity and equality composition. A broad `split_ifs`
in the paired extraction proof exceeded the default heartbeat budget;
splitting only the four coordinate tests and isolating support summation
resolved it. No resource limits, dependency pins or audits were relaxed.

## Algebraic SL2 continuation after checkpoint 03

Continued beyond the character checkpoint with the determinant-based
compact/complex comparison. Executed:

    lake build Math.RepresentationTheory.Audit.AuditSL2ClebschGordan
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Focused build passed (3804 jobs), with ten additional strict transitive axiom
checks and the Math import-layer audit. Full build passed (6920 jobs), without
warning/error lines in `/tmp/sm-sl2-clebsch-build.log`. Layout passed for
1561 modules. Links passed (828 Markdown files, 5082 links, 94 fragments).
Diff check passed. The same-map comparison required explicit induction on
the determinant tensor powers and transport of degree casts; the existing
SU2 injectivity and rank calculations were reused unchanged. No changes to
the physical scope, pins, resource limits or audit policy were made.

## Actual L/Higgs compact Weyl comparison after checkpoint 04

Executed:

    lake build Math.RepresentationTheory.Audit.AuditSL2SymmetricSpan Physics.StandardModel.Operators.Audit.AuditSMLCompactWeyl
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Focused build passed (4145 jobs), including eight Math and nine Physics strict
transitive axiom checks and layer checks. Full build passed (6924 jobs), with
no warning/error lines in `/tmp/sm-compact-full.log`. Only `propext`,
`Classical.choice`, and `Quot.sound` are admitted. Layout passed for 1565
modules. Links passed for 828 Markdown files, 5084 local links, 94 fragments;
the unchanged read-only checker needed an approved retry after sandbox git
subprocess EPERM. Diff check passed.

The actual L restriction, arbitrary-degree exterior source, Higgs spectator,
full local coefficient equivalence and compact-to-kernel equivalence are
checked. No computed multiplicity is a premise. Dependent rewrites of the
large statistical-source carrier initially exhausted default heartbeats;
reusing the existing Weyl inclusion and composing explicit linear-map
identities resolved this without raising resource limits. No CSV values,
dependency pins, physics scope or audit policy changed. The character-counting
adapter remains outstanding, as recorded in the structural result.


## Uniform L/conjugate-L counting after checkpoint 05

Executed:

    lake build Math.RepresentationTheory.Audit.AuditLeptonCounting Physics.StandardModel.Operators.Audit.AuditSMLMultiplicity
    lake build
    python3 tools/exact-rank/check-lepton-weights.py
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Focused build passed (4316 jobs), with 11 Math and 23 Physics strict transitive
axiom checks and layer checks. Only `propext`, `Classical.choice`, and
`Quot.sound` are admitted. Full build passed (6934 jobs), with no warning/error
lines in `/tmp/sm-lepton-counting-full.log`. Layout passed for 1575 modules;
links passed for 829 Markdown files, 5095 local links and 94 fragments. The
unchanged read-only link checker required an approved retry after sandbox git
subprocess EPERM. Diff checks passed.

Kernel-checked controls include the independent LLHH multiplicity 6, central
odd-degree vanishing and exterior-capacity vanishing. The exact rational
script additionally checked zero/top exterior degrees, parity and integral
nonnegative results over 169 degree pairs; these script checks are diagnostic,
not theorem premises or individual CSV certificates. No CSV entries changed.

Source-coordinate and arbitrary exterior continuity, coefficient Hom/Fubini
counting, finite signed-weight extraction, actual neutral local kernel/rank
identities, local support and conjugate charge reversal are proved. Several
initial dependent rewrites on the large statistical-source types exhausted
the default heartbeats; explicit equality composition and generic analytic
transport resolved them without raising resource limits. No dependency pins,
custom axioms, literature premises, audit exceptions or physical scope changes
were introduced. The Q/color A2 prerequisite is documented at the accepted
stop gate in the new result; no all-species completion is claimed.

## Q/conjugate-Q exact-coordinate completion after checkpoint 06

Executed:

    lake build Math.RepresentationTheory.Audit.AuditRationalLocalCoordinates Physics.StandardModel.Operators.Audit.AuditSMQGaussianKernel
    lake build
    python3 tools/exact-rank/check-lepton-weights.py
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check

Final focused build passed (4331 jobs): 21 Math and 28 Physics strict
transitive axiom checks plus import-layer checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are admitted. The final full build passed
(6951 jobs), without warning/error lines in `/tmp/sm-q-gaussian-full-final.log`.
Layout passed for 1590 modules. Links passed for 830 Markdown files,
5110 local links and 94 fragments. The unchanged read-only link checker was
run with an approved sandbox retry after its git subprocess EPERM. Diff checks
passed. The lepton exact rational diagnostic checks still passed over 169
pairs; no new numerical CSV row was asserted from script output.

The new audits cover rational circle infinite order, compact exhaustivity,
Gaussian sample matrices, exterior/monomial coordinate transport, exact
constraint semantics, Gram-polynomial nullity and support, original kernel
rank-nullity, conjugate Q and original unreduced Higgs support. Capacity,
odd-degree and hypercharge controls are kernel-checked. The final four-family original-space
criteria explicitly use the trivial Unit residual input.

Dependent rewriting of statistical-source types initially exceeded default
heartbeats. Equality composition, a generic constant-exterior action lemma
and explicit basis-coordinate transports resolved these failures without
raising resource limits. The explicit symmetric-coordinate sum averages all
representatives of a monomial; nonempty fibers justify the denominator and
avoid supplying an algebraic coordinate map as a numerical input. There are
no custom axioms, `sorry`, literature premises, dependency changes or audit
exceptions. Route A's A2 extraction is not claimed; the accepted symbolic
matrix-family endpoint is supplied by the full-coordinate Route B variant.


## Binary mixed exterior after checkpoint 07

Executed:

    lake build Math.RepresentationTheory.Audit.AuditBinaryPatternExterior Physics.StandardModel.Operators.Audit.AuditSMBinaryContentRanks
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Final focused build passed (4162 jobs): 19 Math and 8 Physics strict
transitive axiom checks, admitting only `propext`, `Classical.choice` and
`Quot.sound`, plus import-layer checks. Full build passed (6958 jobs),
without warning/error lines in `/tmp/sm-binary-full.log`. Layout passed for
1596 modules. Links passed for 833 Markdown files, 5124 local links and
94 fragments. The unchanged read-only link checker used an approved sandbox
retry for its git subprocess. Diff checks passed.

The audited binary statements include graded-product wedge injectivity,
actual image inclusion/surjectivity/equivariance, arbitrary-degree source
dimension and diagonal-character formulas, spectator/supported-coefficient
transport, and SM source/carrier/charge/rank identities with order transport.
Initial proofs encountered dependent species-index casts and additive-instance
diamonds for tensor trace transport. Explicit cast lemmas, pure-wedge map
extensionality and compatible additive-group structures resolved these
without raising resource limits, changing pins or weakening audits.

No numerical CSV values, custom axioms, `sorry`, literature premises or
physical scope changes were introduced. The result is binary mixed-source
decomposition and its consumers, not arbitrary multispecies decomposition
or neutral invariant counting. The latter remaining interfaces are explicit
in the result and continuation plan.


## Mixed-chirality compact comparison after checkpoint 08

Executed:

    lake build Math.RepresentationTheory.Audit.AuditMixedChiralityComparison Physics.StandardModel.Operators.Audit.AuditSMMixedCompactWeyl
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4153 jobs): 19 Math and 24 Physics strict transitive
axiom checks plus import-layer checks. Only `propext`, `Classical.choice` and
`Quot.sound` are admitted. Full build passed (6970 jobs), without warning/error
lines in `/tmp/sm-mixed-chirality-full.log`. Layout passed for 1608 modules.
Links passed for 835 Markdown files, 5137 local links and 94 fragments. The unchanged read-only
link checker used an approved retry for sandbox git subprocess restrictions.
Diff checks passed.

The final audits cover actual paired-to-independent field/source/Higgs
actions, real-form polynomial uniqueness, multilinear orbit polynomials,
transvection exhaustivity, independent-factor spanning and compact comparison,
whole gauge/residual-retaining coefficient spaces, the local actual kernel
and the original arbitrary-Higgs-degree finite reduction. No generic
polynomiality, spanning or multiplicity premise remains on the actual SM source.

Early whole-carrier rewrites exhausted default heartbeats. Generic source/
tensor restriction identities, explicit subtype transports, factor-comparison
lemmas and equality composition resolved these failures without increasing
resource limits. There are no custom axioms, `sorry`, dependency/pin changes,
audit exceptions or new literature/physics premises. CSV values remain
unchanged. Multispecies product dimensions and invariant multiplicity counting
are separate from this completed comparison endpoint.


## Finite-tree exterior iteration after checkpoint 09

Executed:

    lake build Math.RepresentationTheory.Audit.AuditIteratedExterior
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (3338 jobs), with 20 strict transitive standard-axiom
checks and the Math import-layer check. Full build passed (6973 jobs), without
warning/error lines in `/tmp/iterated-exterior-full.log`. Layout passed for
1611 modules. The final documentation link check passed for 837 Markdown files,
94 fragments and 5147 local links. The unchanged read-only checker used an
approved retry for sandbox git subprocess restrictions. Diff checks passed.

The audited theorem constructs arbitrary finite-tree decompositions of actual
selected statistical images, not a conditional decomposition certificate.
Dimensions and character products require finite leaf modules; full-action
decomposition and supported coefficient transport do not. The existing SM
dictionary adapter is explicitly outstanding, so no new SM rank or CSV entry
is claimed.

Early implementations exposed dependent sum-field instance mismatches and
recursive carrier elaboration. Bundled leaf data, canonical sum-family
instances and explicit node/source transports resolved them without raising
resource limits. No custom axioms, `sorry`, dependency/pin changes, audit
exceptions, literature premises or physical scope changes were introduced.


## Ten-species dictionary adapter after checkpoint 10

Executed:

    lake build Math.RepresentationTheory.Audit.AuditPatternSpeciesEquiv Physics.StandardModel.Operators.Audit.AuditSMIteratedContent
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4163 jobs): 26 Math and 12 Physics strict transitive
standard-axiom checks, including constructed dictionaries, content/length
identities, actual-source equivalences, product dimensions/characters and
coefficient/rank-nullity consumers. Both import-layer checks passed.
Full build passed (6978 jobs); `/tmp/sm-dictionary-focused.log` and
`/tmp/sm-dictionary-full.log` have no warning/error lines. Layout passed for
1616 modules. Links passed for 837 Markdown files, 5151 local links and
94 fragments, with zero errors. The unchanged read-only link checker used
an approved retry for sandbox git subprocess restrictions. Diff checks passed.

The field identifications and label bijections are constructed rather than
supplied as SM theorem premises. The length is derived from occurrence counts;
arbitrary words, zero leaf degrees and the empty word are covered by the same
symbolic statements. Source/carrier dimensions are products, not numerical
case tables. Full gauge/Weyl/residual actions and supported coefficient spaces
are retained. Neutral invariant multiplicities and complete support/rank
classification remain open. The CSV and constant-content evaluator are unchanged.

During implementation, dependent recursive degree expressions caused tactic
matching failures despite definitional equality. Explicitly typed append
identities and normalized finite-sum domains resolved these failures without
changing reducibility flags or resource limits. There are no custom axioms,
`sorry`, dependency/pin changes, audit exceptions or new literature premises.
The verified checkpoint remains on the recorded topic branch; no merge or push.

## Conditional Weyl literature input after checkpoint 11

Executed:

    lake build Math.RepresentationTheory.Characters.Audit.AuditCompactWeylExtraction Physics.StandardModel.Operators.Audit.AuditSMWeylExtractionInput
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4298 jobs), with 4 Math and 6 Physics strict transitive
conditional checks and both layer checks. Full build passed (6982 jobs);
`/tmp/weyl-input-focused.log` and `/tmp/weyl-input-full.log` have no warning/error
lines. Layout passed for 1620 modules; links passed for 840 Markdown files,
5165 local links and 94 fragments with zero errors. The read-only link checker
used the approved sandbox-subprocess retry. Diff checks passed.

External source inspected: Woit, *The Weyl Character Formula*, Spring 2012,
sections 1--3, Theorems 1--2 and Corollary 1, including the positive-root
normalization. The derived torus reduction is an explicit unproved parameter,
not a custom axiom. These audits establish only conditional consequences.
Compact comparison, continuity, character presentation and root-coordinate
applicability remain explicit; no complete actual SM input package or neutral
multiplicity table is claimed. See the [result](weyl-input-results.md).

Early kernel-consumer rewrites exhausted default heartbeats by unfolding large
carrier expressions. Equality congruence and separately named dimension
identities resolved the issue without resource or reducibility changes.
There are no `sorry`, custom axioms, audit exceptions or changed dependency
pins. CSV values, earlier checked proofs and root README are unchanged.
The checkpoint remains on the topic branch without merge or push.


## Actual compact extraction application after checkpoint 12

Executed:

    lake build Math.RepresentationTheory.Characters.Audit.AuditFiniteTorusPresentation Physics.StandardModel.Operators.Audit.AuditSMCompactMultiplicity
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4394 jobs), with 20 Math and 31 Physics strict transitive
checks and both layer checks. Full build passed (6991 jobs); no warning/error
lines remain in `/tmp/compact-extraction-focused.log` or
`/tmp/compact-extraction-full.log`. Layout passed for 1629 modules. Final links
passed for 841 Markdown files, 5182 local links and 94 fragments, with zero
errors. The unchanged read-only link checker used its approved sandbox-
subprocess retry. Diff checks passed.

The actual product action, coefficient comparison, analytic model continuity,
six-circle torus homomorphism and finite integer inverse-character presentation
are constructed and audited. The final `SMCompactMultiplicity` conclusions
supply none of those as theorem premises; only the explicit Weyl reduction
input remains. Its strict audit establishes a conditional implication and
does not prove that external reduction/root-maximal-torus Lie specialization.

The polynomial uses noncomputable compact unitarization, torus eigenspace
multiplicities and integer character-lattice choices. It supplies a real
finite semantic presentation but not an executable species-weight recurrence,
numerically evaluated rank list or nontrivial residual classifier. No CSV
values are changed. See [the result](compact-extraction-results.md).

Early attempts with implicit tensor restrictions exhausted default heartbeats;
explicit restricted factors and a reusable product-invariant comparison
resolved them. The finite source continuity proof uses actual pure spans;
explicit coordinate/subtype expressions handle dependent instance matching.
No resource/reducibility flags, dependency pins, custom axioms, `sorry` or
audit exceptions were changed. Root README and previously checked sources
remain unchanged. No merge or push was performed.

## Existing q/l extraction consumer after checkpoint 13

Executed:

    lake build Physics.StandardModel.Operators.Audit.AuditSMQLCompactMultiplicity
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4395 jobs), including 3 strict transitive conditional
checks and the Physics import-layer check. Full build passed (6993 jobs);
`/tmp/ql-extraction-focused.log` and `/tmp/ql-extraction-full.log` contain no
warning/error lines. Layout passed for 1631 modules. Final link check passed
for 843 Markdown files, 5192 local links and 94 fragments with zero errors.
The read-only checker used its approved sandbox-subprocess retry. Diff checks
passed.

`SMQLCompactMultiplicity` composes the existing proved scalar cyclic q/l
charge separation with local extraction. Full test and original all-degree
allowance/forbidden predicates now have only charge neutrality, finite
admissibility and extracted-multiplicity positivity; no residual `Allowed(T)`
remains. The only external mathematical input is Weyl reduction for the
specified tests. This is a finite-predicate characterization, not numerical
support evaluation, an executable classifier or a 572-assignment recount.
Other residual action classes are not included. CSV values and checked
sources are unchanged. No pins, custom axioms, `sorry`, audit exceptions,
root README changes, merge or push were introduced.

## Fixed-input q/l pattern request facade after checkpoint 14

Executed:

    lake build Physics.StandardModel.Operators.Audit.AuditSMQLPatternRequests
    lake build
    node tools/layout/check-layout.mjs
    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Focused build passed (4413 jobs), with 13 strict transitive standard-axiom
checks and the Physics layer check. Full build passed (6995 jobs). No
warning/error lines remain in `/tmp/ql-pattern-focused.log` or
`/tmp/ql-pattern-full.log`. Layout passed for 1633 modules. Final links passed
for 845 Markdown files, 5202 local links and 94 fragments with zero errors.
The unchanged read-only checker used its approved sandbox-subprocess retry.
Diff checks passed.

The new finite actual-coefficient family is proved equivalent at the support
level to the original all-degree selected content/Higgs spaces, including
vanishing above degree 180 and each allowed target's own witness. The B/L
selector matches the existing signed convention. `Request` data are reused;
`b1_b2_original_iff` validates the B1-forbidden/B2-allowed meaning independently
of extraction. Multiplicity-based conditions remain conditional on Weyl
reduction; `forbid_of_charge` does not use that input. No concrete q/l charge
assignment is certified as satisfying this request by defining the request.

The catalogue now routes compatible fixed q/l inputs through this facade.
Checked generic, BGW charged-Higgs and DGT prescribed-LFV sources remain intact.
Spectral evaluation is still noncomputable and the finite table is not
materialized. No table values, pins, resource settings, custom axioms, `sorry`,
audit exceptions, root README changes, merge or push were introduced.

## README input-route documentation after checkpoint 15

At the user's explicit request, the root README now links the fixed q/l
pattern facade, general action/domain inputs, model-specific mixed requests
and prescribed LFV selectors. It states the Weyl input and noncomputable
multiplicity boundary, and replaces the obsolete open uniform-cutoff claim
with the proved finite reduction and conditional q/l support criterion.

Executed:

    node tools/docs/check-links.mjs
    git diff --check
    git diff --cached --check

Links passed for 845 Markdown files, 5212 local links and 97 fragments with
zero errors; the read-only checker used its approved sandbox-subprocess
retry. Diff checks passed. This is documentation-only: no Lean build or axiom
audit was rerun, and no new proof baseline is claimed. No source, assumption,
dependency or table value changed. No merge or push was performed.

## Master integration at stage 01

The user explicitly authorized master integration. Topic tip `checkpoint 16` was
merged with `git merge --no-ff proof/sm-rank-certificates` as `checkpoint 17`, from
master `checkpoint 18`. Master had no independent commits to reconcile and the
worktree was clean. The merge had no conflicts. It includes the related
SM/Higgs cutoff, scalar q/l separation, local/statistical finite kernels,
SU3 generation, bounded rank enumeration and LLHH prerequisite chain; the
original parent targets in their topic records remain historical metadata.
No unrelated branch was merged. Lean and dependency pins are unchanged.

Merged-state checks:

- `lake build`: passed, 6995 jobs, no warning/error lines in
  `/tmp/sm-support-master-build.log`.
- `lake env lean <audit file>` rerun serially for all 39 added audit files
  from the recorded inventory of changed audit modules, plus the
  existing `AuditInverseCyclicFollowups`: all 40 passed, with 646 strict
  transitive checks and no warning/error lines in
  `/tmp/sm-support-master-audits.log`.
- `node tools/layout/check-layout.mjs`: 1633 modules passed.
- `python3 tools/exact-rank/certify.py tools/exact-rank/examples.json --check
  Math/LinearAlgebra/ExactRankCertificateExamples.lean`: exact regeneration
  matched.
- `python3 tools/exact-rank/check-lepton-weights.py`: 169 exact degree pairs
  passed the stated controls.
- `python3 tools/sm-rank-enumeration/enumerate.py`: committed bounded q/l CSV
  controls passed, including 572 candidates and 151 unit orbits. These are
  bounded predicates, not an all-degree numerical support verdict.
- `lake env lean tools/exact-rank/constant-content-table.lean`: output compared
  byte-for-byte with the committed constant-content CSV and matched.
- `node tools/docs/check-links.mjs`, `git diff --check` and
  `git diff --cached --check`: passed after integration-record updates;
  845 Markdown files, 5221 local links and 106 heading fragments, zero errors.
  The read-only link checker used its approved sandbox-subprocess retry.

The Weyl torus reduction remains an explicit literature theorem parameter.
Noncomputable spectral multiplicities and the conditional finite support
criterion do not supply concrete all-content numerical ranks or an executable
model classifier. Integration does not change those boundaries.

After merged-state verification, reachability from master, worktree non-use
and absence of unmerged child refs were checked. The eight local branches
from `proof/sm-higgs-support-cutoff` through `proof/sm-rank-certificates`
listed above were safely removed with `git branch -d`; historical branch
names remain in their records. The unrelated detached worktree and other
branches were preserved. No remote push or remote branch deletion occurred.
