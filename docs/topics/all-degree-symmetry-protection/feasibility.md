# Bounded Literature Feasibility Decision

Date: stage 01. Both named routes in each planned pass were inspected.
This decision closes the bounded investigation; it does not prove R1/R2.

## Source And Package Baseline

- Mathlib: `1a547d8a48a8fa7877d2decb69d7294723bb0187`.
- TauCeti: `b9e2e182804073eb92718b68a9baf37df8e189bd`.
- Pins and dependencies unchanged. Inspection combined rg searches and source
  reads; no package-wide build or claim of absolute library absence is made.

## C1 — Symmetric-Power Occurrence And Branching

R1 Eq. (4.30) tests occurrence of nontrivial larger-group representations with
smaller-group fixed vectors. Its Eq. (4.32) then replaces occurrence at any
polynomial degree by generic-stabilizer fixed vectors. Existing compact
semisimplicity, symmetric-square results and subgroup restriction do not prove
this replacement for an arbitrary field representation at all degrees.

Inspected TauCeti `ClassicalGroups/SymmetricPower.lean` and
`ClassicalGroups/Weight/SymmetricPower.lean`: they supply standard-GL symmetric
power actions, diagonal character formulas and weights. These are useful for
specified representations, not the needed arbitrary-representation occurrence
classification. Compact `Invariants.lean` supplies character-integral counting
at a specified representation, not a finite all-degree structural test.
Stage A gives the exact invariant-space comparison without that replacement.

Decision: stop the general friendship implementation at the missing
all-degree occurrence-to-generic-stabilizer theorem. A conditional occurrence
criterion would leave that main premise unproved, so it is not reported as
friendship certification. No bosonic formula is extended to fermions.

## C2 — Generic Stabilizer And Covariant Rank

The original Brion R4 Sec. 1.2 corollary (printed p. 4) was located. Its setup
uses reductive algebraic groups and rational actions on finite-type algebras;
the corollary assumes irreducible X and a generic closed orbit isomorphic to
G/H, and identifies covariant module rank with dim(M^H). Its proof uses the
quotient fibers and regular functions on G/H.

The relevant searches in project and pinned representation/invariant-ring
sources found no ready theorem connecting this setup to the present abstract
representations. `RingTheory/Invariant/Basic.lean` concerns finite-group
invariant extensions and prime ideals. TauCeti `Induction/Inertia.lean` uses
“generic stabilizer API” to mean the ordinary stabilizer of an action; it is
not the algebraic-geometric generic stabilizer of R4.

Decision: new foundations for rational algebraic actions, generic closed
orbits and the covariant-rank bridge would be a separate milestone. This
route hits the recorded scope gate. The closed-orbit hypothesis must not be
dropped from any later proposed translation.

## D1 — Explicit Polynomial Evaluation

Implemented coordinate-polynomial covariants, their actual stabilizer and a
linear evaluation map into its fixed subspace. This contains no genericity
premise. Constants prove saturation for a trivial target at every value;
a degree-one scalar covariant proves saturation at every nonzero value in
the weight-one single-coordinate example. The zero-value calculation shows
why the value and its actual stabilizer must be tracked together.

Decision: the elementary evaluation endpoint and bounded exact examples are
feasible and proved. They are not a full comparison with R2's MLFV EFTs.

## D2 — General Saturation

R2 Sec. 2.2 Eq. (2.8) reasons through covariant module rank. To formalize the
pointwise evaluation statement one must additionally establish the exact
hypotheses giving the evaluation image at an admitted value. The original
R4 rank corollary is not by itself a theorem about every evaluation map.

Source searches for covariant/generic-stabilizer and evaluation-surjectivity
were checked against relevant files. TauCeti's Clifford
`Induction/Clifford/TensorFactorization.lean` has an `evalTensor_surjective`
theorem for representation tensor factorization, not polynomial evaluation
at a spurion value. Mathlib MvPolynomial evaluation and representation fixed
spaces suffice for D1, but no ready general saturation bridge was identified.

Decision: stop general saturation at the same algebraic-geometric prerequisite
and the separate pointwise image theorem. Do not add R2/R4 as unproved premises.
Before reopening, specify compact versus complexified algebraic groups,
conjugate coordinates, the principal/generic locus and evaluation theorem.

## Reference Correction Audit

R3's published Erratum was read. It corrects Eqs. (2.113c) and (2.113d) and
removes a claim about powers of secondary invariants in the text below
Eq. (2.15). Its authors state that conclusions are unaffected. None of those
branching tables or secondary-invariant claims enters the present proofs.
See the pinned links and inspection status in [references](references.md).

## Stop And Remaining Work

The mathematical stopping condition has been reached for general friendship
and saturation. Complete verification/documentation of the implemented A/B
and D1 results, then commit. New foundations, UV model searches, actual-light
mass bridges and derivative/EOM/IBP work are not automatic continuations.
