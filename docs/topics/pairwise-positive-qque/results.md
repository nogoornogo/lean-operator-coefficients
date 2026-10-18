# Two Pairwise Constituents Suffice

## Endpoint

[PairwisePositiveQque](../../../Physics/StandardModel/Operators/PairwisePositiveQque.lean)
constructs an actual-field qque coefficient with nonzero alternating descent
and an invariant fourth-exterior-power functional under SM-cover x H x SL(2,C).
It requires positive support shared by Q/up and by Q/e, not a constituent
shared by all three:

```text
PairwisePositive a := exists i k,
  a_Q(i) > 0 and a_up(i) > 0 and a_Q(k) > 0 and a_electron(k) > 0.
```

i and k may be equal or different. Coefficient values need not coincide, and
there is no equality-of-characters or positive-total-dimension premise.
`of_shared` proves that the previous three-way shared-positive condition
implies this one. Older common-index and conjugation recovery lemmas therefore
still apply through that implication, without changing previous proofs.

## Source Conditions

The input retains the finite-dimensional ambient representation and symmetric
T x H mass interface, and a jointly continuous compatible SM-cover x H action
on its unchanged radical K. H is compact. The finite normalized family S_i
consists of pairwise inequivalent continuous irreducible complex representations
on finite-dimensional normed carriers.

Three `VirtualSMSpeciesIndex.SpeciesMatches` equations identify the actual
Q, upRight.dual and electronRight.dual multiplicity indices with the supplied
signed profiles. The opposite-species dual terms are retained, and equality
is for every h in H, not just for dimensions. Automatic normalized
presentation construction is still outside this interface.

The direct endpoint needs no T-unitarity, four-weight matching or actual
conjugation premises. This is not a claim that any given ambient model meets
the species equations or pairwise support. No SM field decomposition,
splitting maps, invariant coefficient or exchange-symmetry certificate is
assumed at the source endpoint.

## Nonzero Symmetrization

[PairwiseInvariantPairing](../../../Math/RepresentationTheory/PairwiseInvariantPairing.lean)
allows two split quotients R and S of the same Q multiplicity representation A.
For projections p_R and p_S, the coefficient is

```text
phi(p_R(x)) psi(p_S(y)) + phi(p_R(y)) psi(p_S(x)).
```

It is symmetric in x,y and equivariant for arbitrary H. No orthogonality,
inequivalence or vanishing cross-projection hypothesis is used. A vector x
with both projections nonzero exists: take either of two split lifts if it
works for both projections, otherwise their sum. Dual functionals can then
be chosen to evaluate to 1 on each projection. The diagonal coefficient is 2.

[PairwiseQqueSpinorExterior](../../../Physics/StandardModel/Operators/PairwiseQqueSpinorExterior.lean)
combines this coefficient with the existing gauge and left/right spinor
contractions. On a concrete four-slot witness its alternating descent is 4.
Although the Q flavor vector is reused, its color/weak/spin components differ;
this does not assert nonzero exterior powers of a repeated identical field
vector. The proof covers the equal-constituent case as well, without a new
minimum-generation assumption.

[Species extraction](../../../Physics/StandardModel/Spectrum/PairwisePositiveSpeciesIndex.lean)
derives four split maps from the two positive-support pairs. It uses the
existing compact character/Hom-dimension identity separately for each index.
Actual SM field extraction and alternation transport then return the
coefficient to participating subspaces of K and K.dual with spinors.

## Controls And Scope

The [Lean audit](../../../Physics/StandardModel/Operators/Audit/AuditPairwisePositiveQque.lean)
uses H = Circle with distinct trivial and standard characters 1,z. The actual
multiplicity representations are Q=1+z, up=1, e=z. Their characters match the
specified profiles, which have pairwise but no three-way positive support.
The resulting explicit SM x H spinor-field model has nonzero exterior descent.
This is a concrete representation/field-model control, not an ambient GUT
representation, invariant mass and radical realizing the entire source API.

A missing-pair control Q=up=1, e=z fails `PairwisePositive`. It is not a
general theorem that failing this sufficient condition forbids qque.
`same_quotient` identifies the new internal coefficient with the previous
coefficient when the Q projection is reused for both pairs.

The [exact two-flavor computation](../../../tools/qque/audit_pairwise.py)
checks all four-slot antisymmetrizations on 32 component generators against
an independent Grassmann expansion: 48 nonzero monomials, absolute coefficient
2, and value 4 for the common-vector diagonal witness. It is a cross-check,
not a Lean proof premise. The prior one-generation computation also remains.

This supplies a strictly weaker support condition at the representation-data
level, not a new phenomenologically viable model or embedding classification.
No Wilson coefficient generation, anomaly consistency, decay amplitude,
finite lifetime or change to the E6 literature boundary is claimed.

See [verification and integration](README.md).
