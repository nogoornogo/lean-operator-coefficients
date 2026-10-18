# Structural exterior characters and A1 extraction

This record describes the character and compact comparison milestones. The
subsequent [L/conjugate-L result](lepton-multiplicity-results.md) now closes
their local support criterion uniformly. The rank CSV remains unchanged.
The working branch and integration target remain those in the topic overview.

## Exterior characters

[ExteriorCharacterPolynomial](../../../Math/RepresentationTheory/ExteriorCharacterPolynomial.lean)
proves, over any commutative ring, that the degree-n coefficient of

    product_i (1 + a_i * t)

is the sum of products over n-element subsets of the basis indices. The
include/exclude recurrence `coeff_insert` is also proved symbolically.
`exterior_character` connects this polynomial to the character of the actual
exterior representation when the chosen group element is diagonal in the
given basis. The proof uses the pinned TauCeti exterior trace theorem; it
does not reprove or claim ownership of that theorem.

## Actual SM source connection

[SMConstantSourceCharacter](../../../Physics/StandardModel/Operators/SMConstantSourceCharacter.lean)
transports the formula through `ConstantPatternExterior.equiv`.
`weak_character` works for every species and every exterior degree, with
arbitrary supplied residual flavor representations (the residual element at
which the character is evaluated is the identity).

For L, `lepton_character_product` retains independent weak and actual left-Weyl
torus variables z,w and proves the following for every n:

    character(Source(L^n))(z,w)
      = [t^n] product_{e,f in {+1,-1}} (1 + t*z^e*w^f)^3.

The exponent three is the number of flavors. Only the fixed two-dimensional
basis coordinates are split; n is never specialized. This is the actual
statistical source, not an unrestricted tensor power. Higgs multiplication,
conjugate-L transport and coefficient-space multiplicity remain to be connected.

## Structural SU(2) multiplicity functional

[SU2WeightExtraction](../../../Math/RepresentationTheory/SU2WeightExtraction.lean)
defines symmetric weight pairs P_0(z)=1 and P_k(z)=z^k+z^(-k) for k>0.
If a class function restricts to sum_k c_k P_k on the torus, with finitely
supported complex coefficients, `integral_of_weight_expansion` proves

    HaarAverage(f) = c_0 - c_2.

`invariant_finrank` identifies this scalar with the complex-cast dimension of
Hom(trivial,rho) for a finite-dimensional jointly continuous representation.
The normed-space structure and joint continuity are explicit hypotheses.
The theorem concerns invariant vectors; applying it to invariant coefficient
spaces still requires the appropriate dual/transport connection.

For two independent SU(2) variables, `integral_pair_of_weight_expansion`
proves the iterated-average formula

    c_(0,0) - c_(0,2) - c_(2,0) + c_(2,2).

Its hypotheses are conjugation invariance in each variable and the finite
two-variable weight-pair expansion. It does not assume a computed rank.

The proof writes a nonzero weight pair as chi_k - chi_(k-2), with the degree
one boundary handled separately, and integrates these characters. It reuses
TauCeti's `integral_character_symPower`, torus conjugacy, and the existing
`CompactHomDimension` adapter. The pinned SU2 Weyl/Exhaustion files were
available but had not been built before this milestone. No dependency pin
was changed. The two-factor proof is an iterated integral, not an unproved
identification with an actual SL(2,C) invariant space.

## Counting continuation and acceptance boundary

These results close the general exterior-character identity and provide the
A1 extraction functional. The following counting obligations were open at
the character checkpoint and are now discharged for L/conjugate-L in the
linked result:

1. Construct the finite two-variable weight-pair coefficients of the L/Higgs
   character uniformly, with the required symmetry and continuity adapters.
2. The L statistical-source and L/Higgs compact/full Weyl comparison is now
   proved, as described below; the subsequent result supplies conjugate-L
   coefficient transport.
3. Transport the invariant-vector/dual statement to the actual coefficient
   kernel, account for hypercharge, and derive the degree-uniform multiplicity
   and support theorem. Then transport conjugate L. Q additionally needs A2.

The algebraic construction for step 2 has now advanced beyond feasibility:
[SL2SymmetricEmbeddings](../../../Math/RepresentationTheory/SL2SymmetricEmbeddings.lean)
and [SL2ClebschGordan](../../../Math/RepresentationTheory/SL2ClebschGordan.lean)
extend the determinant-based construction to the actual complex special
linear group. The new `embedding_linearMap` and `assemble_linearMap` theorems
identify the underlying maps with the checked SU2 construction, so injectivity
and dimension equality are reused rather than assumed. `equivalence` is an
SL(2,C)-equivariant Clebsch–Gordan decomposition at all two-factor degrees.

The two `coefficient_fixed_of_compact` theorems prove compact invariance implies
SL(2,C) invariance for a coefficient on any symmetric power and on any tensor
product of two symmetric powers. These are degree-uniform actual-group
results; they need no continuity or literature premise.

[SL2SymmetricSpan](../../../Math/RepresentationTheory/SL2SymmetricSpan.lean)
now proves closure of symmetric-power spanning under tensor products and
surjective equivariant maps. `tensorPower` proves the property for every
iteration degree; `exterior` descends it through TauCeti's canonical
surjective tensor-to-exterior map. `coefficient_fixed_of_compact` then proves
compact-to-SL2 invariance for every representation with this spanning property.
No irreducible multiplicities need to be selected or computed.

[SMLCompactWeyl](../../../Physics/StandardModel/Operators/SMLCompactWeyl.lean)
proves that the actual L field restricted to the Weyl factor has this property:
the gauge and flavor factors are trivial for that restriction and the spinor
is the standard doublet. `source_spanned` transports the exterior result to
the actual constant-content statistical source. `higgs_spanned` retains the
actual Higgs constituent for arbitrary n, m and hypercharge index delta.
`local_coefficient_fixed_iff` preserves all local gauge conditions while
restricting only the Weyl factor to SU2. `coefficientEquiv` identifies the
entire coefficient spaces, and `compactKernelEquiv` maps the compact local
coefficient space to the actual finite constraint kernel.

The supplied residual flavor representation is arbitrary, but local invariance
sets its group element to the identity. This theorem does not classify residual
invariants or replace them by an unrestricted multiplicity. It does not assert
compact comparison for mixed left/right chirality. The subsequent counting
adapter now instantiates compact continuity, connects coefficient Hom
integration to the two-variable Haar functional, handles hypercharge, and
constructs finite weight-pair coefficients uniformly. The resulting nullity
formula and conjugate transport are documented in the linked L/conjugate-L
result. No numerical CSV row was changed. Persistent audits:
`AuditSL2SymmetricSpan` and `AuditSMLCompactWeyl`.

No numerical certificates are used to replace the structural endpoint. No
new physical inputs, literature axioms, unproved rank premises or changes to
the Lean/dependency pins are introduced. Audits are registered in Math and
Physics. See [verification](verification.md) for executed checks.
