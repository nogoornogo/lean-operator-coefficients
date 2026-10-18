# Frozen Plan

## Statement Contract

Keep finite species alphabets and the existing local/residual representations
fixed. A content specification is a predicate on ordered species contents at
each mixed degree, with proved permutation stability. The predicate selects
coefficients being tested for prohibition; it is not an extra gauge-invariance
condition. A detector is a permutation-stable map to an information type.
Pulling any target predicate back along a detector produces a specification.

A charge dictionary is one detector into an arbitrary additive abelian group.
Use integer 3B/L labels for SM examples and explicitly distinguish signed
changes, absolute changes and conjugates. Prohibiting both classes means a
union (logical OR); intersection selects operators satisfying both changes.
An intersection does not represent prohibition of each class separately.

General coefficient selectors are linear maps from an admitted invariant
coefficient space to independently supplied targets. They are a separate
interface: not every selector is expressible as species content or charge.
LFV selectors require an admitted flavor convention. No universal flavor or
mass basis is inferred.

## A — Stable Content Specification Algebra

Provide predicate pullback along stable detectors, empty/full specifications,
union, intersection, complement and indexed union, with stability proofs.
Reuse `MixedChargeSelection.charge` and `charge_stable` for charge detectors.
Avoid an unnecessary replacement of the existing `allowed` API; provide
adapters to it. Decidability is supplied or classical only where required.

Prove prohibition of a union iff prohibition of each constituent, degreewise
and at all degrees, using the existing constructed factor characterization.
Prove monotonicity under target inclusion and that an intersection inherits
prohibition from either constituent. Do not assert an intersection iff.
Treat all-degree products and finite-support families distinctly; transfer
prohibition with existing comparison results rather than equating the spaces.

## B — Symmetry And Selection Consumers

Instantiate existing selected completeness and restriction maps using the
specifications. Derive the union law for symmetry extension from contentwise
restriction surjectivity, if the existing factor interface suffices. Preserve
the natural restriction map and independently defined input action.

Provide a reusable prohibition certificate consumer for a detecting character
on each selected content. Different constituent specifications may use different
detecting elements. Derive simultaneous prohibition by composition; no
neutrality-to-existence converse or automatic search algorithm is claimed.

## C — Linear Selector Composition

On one fixed coefficient domain, combine a family of linear selectors into
a product selector and prove vanishing iff every component vanishes. Prove
transport through the supplied completeness equivalence and check compatibility
with restriction when a commuting selector square is supplied.

Do not extend a selector across a different field domain by assumption. A
content-selector identification, when wanted, needs a proved dictionary; the
abstract product-selector result alone is not a physical LFV theorem.

## D — Existing Input Regression

Inspect the existing signed SM/Higgs BNV dictionary once. Reuse its proved
field/action identifications. Define the simultaneous detector `(3B,L)` from
existing species labels, including boson/conjugate labels as admitted by that
input. Prove permutation stability and recover the old nonzero-B support.

Show that switching between `abs(3B) in {3,6}` and
`abs(3B)=3 OR abs(L)=2` changes only the target predicate on this dictionary.
Provide extraction/reconstruction compatibility and a consumer with explicit
scalar-action/detection hypotheses. A concrete example must prove its action
hypotheses; it must not be presented as a protecting UV model.

Inspect the existing dipole interface in one bounded adapter pass. Reuse a
selector if its actual domain has a ready completeness bridge. Otherwise record
the precise missing bridge and stop that adapter. No new dipole-to-mixed-field
foundation or physical mass-basis project is authorized.

## Acceptance And Stop

Sources belong under Math for specification/selector algebra and Physics for
the admitted SM regression. Register aggregates and persistent strict transitive
axiom/layer audits. Controls distinguish OR from AND, overlapping contents,
empty targets and neutral but locally forbidden contents where existing APIs
permit reuse. Do not rely on dimension counts as semantic dictionaries.

Run focused builds and audits, one serialized full `lake build`, layout and
local-link checks, and unstaged/staged `git diff --check`. Update the topic,
current dossiers and assumptions only for verified results; commit the endpoint.

Stop after A–C, the SM regression and the bounded dipole adapter outcome are
verified. Do not search for UV models, reopen generic geometric foundations,
or change toolchain pins. A new theorem-level dictionary prerequisite beyond
the existing interfaces is a documented scope stop, not permission to start
another foundational project. Master integration requires explicit direction.
