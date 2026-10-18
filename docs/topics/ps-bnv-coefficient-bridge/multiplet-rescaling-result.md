# Specified Whole-Multiplet Scalar Changes

For one generation, choose nonzero complex a,b,h and new coordinates
xi'=a xi, fR'=b fR, chi'=h chi. Scalar multiplication commutes with each
complex-linear group action; this is not a classification of all possible
PS-equivariant changes. See the [plan](multiplet-rescaling-plan.md) and
[verification](multiplet-rescaling-verification.md).

[DisplayedKernelComparison](../../../GUT/PatiSalam/Matching/DisplayedKernelComparison.lean)
defines y'=y/(star(a)*star(h)*b). `rescaled_vertex` proves direct substitution
in the barred Yukawa monomial recovers its original coefficient. This
commuting coordinate identity fixes the scalar prefactor only; it does not
substitute for the noncommutative Grassmann action.

With v'=h*v, `rescaled_mixing` proves

```
y' * star(v') = (y * star(v)) / (star(a)*b).
```

Thus neutral mixing and the colored vertex use the same transformed coupling.
Define vR'=sqrt(2)*v' in the new coordinates too. For y,v,a,b,h nonzero,
`rescaled_norm_discrepancy` proves

```
norm(y' * vR') != norm(y' * star(v')).
```

This allows complex VEV coordinates after rephasing; norm removes conjugation.
It preserves the missing-sqrt(2) comparison under these specified scalar
changes. It does not assert that y*vR itself is numerically unchanged when
fermions are rescaled. Nor does it preserve the old mode's coordinates or
remove the need to transform kinetic metrics when interpreting physical masses.

The local normalization comparison is complete for this family. Multiple-copy
mixing, general kinetic metrics, conjugate/dual field identifications and full
signed coefficient matching remain outside. No rate scaling is inferred.
The [common-scale result](common-scale-result.md) and
[older connection](connection-result.md#what-the-convention-test-establishes)
are complementary tests, not independent paper-wide error certificates.

## Reporting Status

Author notification and any separate public report of the local normalization
discrepancy are undecided. No author response or external notification is
recorded. Subsequent numerical calculations, rates and bounds have not been
verified; no consequence for their numerical values is certified. These
reporting decisions are separate from the verified local comparison.
