# Results

## Completed Construction

For arbitrary natural fermion/boson degrees, finite species alphabets and complex
local/multiplicity modules, the coefficient space is classified by a product of
residual-Hom factors on constructed carriers

`Q_c = ((L_c)_G ⊗ M_c) / R_exchange`.

The principal theorem has no local spanning certificate, chosen contraction
basis, finite-dimensional multiplicity, compactness or semisimplicity premise.
Local/residual actions act on separate tensor factors and their commutation is
proved. The signed fermion and unsigned boson exchange relations are generated
on actual heterogeneous ordered tensors, transported and quotiented explicitly.
Restriction, assembly and quotient Hom descent provide both inverse maps.

`GradedMixedCompleteness.equiv` handles all contents of a fixed mixed degree;
`selectedEquiv` handles any separately permutation-stable support, including
additive charge and engineering selections. `allEquiv` identifies the product
of degree coefficient spaces with functionals on the direct sum of residual
carriers. Its zero/nonzero iff and `all_bounds_forbidden_iff` distinguish an
all-degree criterion from a finite decision cutoff. `MixedContentBounds.bounded_finite`
proves finiteness of contents under positive weights, including both slot counts.
That finiteness lemma is separate from the graded equivalences and the
all-bounds iff, which does not require positive weights. No combined single-
bound finite-index equivalence is packaged by this coefficient-space decomposition theorem.

## Actual Consumer

`GradedBnvComparison.perDegreeEquiv` starts from the independent actual SM/Higgs
BNV support. Both baryon signs and all ten signed species are retained; opposite
multiplicities and both scalar residual actions are independent.
`sixComparison` and `sevenComparison` identify generic degree factors with the
old explicit residual coordinates. `boundedSevenEquiv` combines the generic
content maps with the old proved degree decomposition, not its coefficient
dictionary. The overall comparison is canonical transport through the same
actual coefficient space. Extraction/reconstruction commute, and both inverse
laws and prohibition/nonzero iff are proved.

The actual-field additive instance is aligned with the standard tensor-product
instance so that the generic and existing carriers share a coherent algebraic
interface. This changes no hypotheses, charges or group actions; the existing
six/seven theorems are rebuilt and the new comparisons are audited.

## Acceptance Regressions

`MixedCompletenessExamples` proves two-boson exchange on the generated quotient,
the mixed two-fermion/two-boson exchange sign, and vanishing with repeated
fermion inputs. It also constructs the separated-quotient equivalences and
checks reconstruction for these degrees. Degree equalities are kept explicit
in the dependent inverse-law interface; the tests do not enumerate permutations
or rely on sampled values. The equivalence records include both inverse laws.

## Completed-Result Documents

- [General mathematical theorem](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md)
- [Actual SM comparison](../../proof/current/applications/Physics/GRADED_BNV_COMPARISON.md)
- [Math assumptions](../../proof/current/inputs/Math/ASSUMPTIONS.md)
- [Physics assumptions](../../proof/current/inputs/Physics/ASSUMPTIONS.md)

## Boundaries

No AutoEFT installation, dependency change, new external mathematics premise,
dimension-eight-to-eleven basis enumeration, derivatives, field strengths,
EOM/IBP, amplitude, matching or rate result is added. The theorem gives a
degree-uniform algebraic iff, not an algorithm computing arbitrary residual Hom,
a finite all-degree cutoff, a graded-ring multiplication API, or unconditional
inevitable BNV. Master integration was explicitly authorized after completion;
Git ancestry is the authoritative integration record.

## Verification

The [topic overview](README.md) records the final focused/full build and strict
audit evidence. All commands run from the repository root with pinned tools on PATH:

```sh
lake build Math.RepresentationTheory.Audit.AuditGradedOperatorFoundations Physics.StandardModel.Operators.Audit.AuditGradedBnvComparison
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```
