# Mixed-chirality compact comparison

The actual paired Weyl coefficient invariance is equivalent to invariance
under independent compact left/right SU2 actions. This is proved for every
signed SM species pattern, every exterior degree and every one-doublet Higgs
constituent. No single-chirality assumption, numerical multiplicity, density
premise or symmetric-power spanning premise is left on the actual source.

Gauge and arbitrary supplied residual conditions can be retained: the entire
original full invariant coefficient space is identified with the submodule
satisfying those unchanged conditions and the independent compact Weyl tests.
There is also a local version and a whole-space equivalence with the previously
proved actual finite kernel. This closes the requested mixed-chirality
comparison interface, while invariant counting remains a separate obligation.

## Exact statement and group conventions

[WeylIndependentAction](../../../Physics/FieldTheory/Spinor/WeylIndependentAction.lean)
uses the independent complex group `SL2(ℂ) × SL2(ℂ)`. A left slot uses its
first factor and a right slot its second. The actual real-form homomorphism
is `g ↦ (g, conjugate g)`; the right action is entrywise conjugation, matching
`WeylSpinor.right`. The independent compact map is

    SU2 × SU2 -> SL2(ℂ) × SL2(ℂ).

It is not restriction to a single diagonal SU2. The two independent factors
are essential for a correct mixed-chirality invariant comparison.

In [SMMixedCompactWeyl](../../../Physics/StandardModel/Operators/SMMixedCompactWeyl.lean),
`field_paired`, `source_paired` and `action_paired` identify the independent
action pulled back along the real form with the actual field, statistical
source and source/Higgs Weyl action. `coefficient_fixed_iff` proves, for any
linear coefficient f on the actual carrier,

    f fixed by the actual Weyl action
      iff f fixed by the independent compact left/right action.

Degrees and content are symbolic. Three-generation flavor modules are kept;
their supplied residual representations are arbitrary. Restriction to the
Weyl factor sets the other group elements to the identity; it does not erase
them from the subsequent full coefficient-space comparison.

## Proof structure

[PolynomialRealForm](../../../Math/RepresentationTheory/PolynomialRealForm.lean)
proves that a complex polynomial in two variables vanishing on every
`(z, conjugate z)` is zero. Substitution by `X0 + i*X1` and `X0 - i*X1` reduces
the premise to a polynomial vanishing on the real-coordinate grid. Mathlib's
`MvPolynomial.funext_set` applies because each real side is infinite. The
invertible linear coordinate substitution then gives uniqueness on all
complex pairs. No general Zariski-density theorem is imported or assumed.

`PairedPolynomialInvariants` uses this uniqueness and actual transvection
generation to separate the two group factors. Its generic orbit-polynomial
hypothesis is discharged by `BiaffineStatisticalOrbits`: the multilinear
include/exclude expansion has one variable per chirality, descends through
the surjective actual statistical-source map, and retains fixed Higgs
spectators. `source_polynomial` and `action_polynomial` instantiate this for
the actual signed SM fields. No rational chart or denominator hypothesis is
needed.

`SL2StatisticalSpan` proves symmetric-power spanning for the finite species
module and arbitrary selected statistical images using the existing SL2
spanning results, equivariant species inclusions, exterior powers and the
existing statistical projection. Applied separately to each independent
factor, one spin chirality is standard and the other is trivial. The existing
compact-to-complex coefficient theorem therefore applies to both restrictions.
`SL2PairCompactComparison` assembles them. There is no irreducible
multiplicity selection or classification assumption in this argument.

`StatisticalSourceRestriction` supplies generic source/tensor restriction
identities to keep actual-source type transports small and explicit.

## Whole coefficient-space and original Higgs connections

[SMMixedCompactCoefficients](../../../Physics/StandardModel/Operators/SMMixedCompactCoefficients.lean)
defines `FullSpace` as a submodule of actual linear coefficients subject to:

- the original gauge and supplied residual action, with Weyl element 1;
- the independent compact Weyl action on the same source/Higgs carrier.

`fullEquiv` identifies the original full invariant coefficient space with
this submodule, by the identity on linear maps. `localEquiv` does the same
when retaining only the local gauge conditions. `kernelEquiv`,
`kernel_dimension` and `allowed_iff` connect that local compact constraint
space to the existing actual finite kernel, preserving both dimension and
support.

These spaces are explicit simultaneous invariant conditions. This result
does not construct a new combined compact product representation or prove
its continuity/Haar-character counting interface. Such a counting adapter
must be justified separately rather than inferred from the submodule name.

`original_allowed_iff` connects arbitrary original Higgs degrees h,d to the
already proved finite source bound: a constituent must be admissible and its
`FullSpace` must have a nonzero coefficient. This retains the arbitrary
residual condition and full-field statistics. It is a finite reduction of
support, not a completed decision of the remaining `Allowed FullSpace`.

## Completion boundary

The requested comparison is proved for arbitrary contents, including three
or more species, without relying on an unproved multispecies exterior-product
decomposition. The independent compact Weyl coefficient conditions and the
actual paired conditions are now equivalent. There are no added dependencies,
pin changes, custom axioms, literature premises or numerical certificates.

Arbitrary multispecies product dimensions, A2 invariant extraction, numerical
mixed-content ranks and residual q/l classification remain outside this
result. No CSV entry changed. See the [plan](mixed-chirality-plan.md) and
[verification](verification.md).
