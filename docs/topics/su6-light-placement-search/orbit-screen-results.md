# Z5 Equivalence Reduction and Fixed SU(6) Admission

The [frozen orbit screen](orbit-screen-plan.md) is complete. The twenty
previous charge assignments represent five orbits under common multiplication
by nonzero Z5 elements. This is the declared generator-change equivalence,
not an assertion that different UV field spectra are equivalent.

## Representatives

Normalize the nonzero qque charge to one by multiplying all charges by its
inverse. Each orbit has four elements and exactly one such representative.
The [exact enumeration](../../../tools/su6-light-placement-search/check_z5_orbits.py)
checks disjoint orbit coverage and unique normalization for all twenty inputs.

| Q | U | D | L | E | H | qque charge | Prior scalar/block SU(6) phase fits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 1 | 4 | 1 | 3 | 4 | 1 | 0 |
| 1 | 2 | 1 | 3 | 4 | 2 | 1 | 0 |
| 2 | 3 | 3 | 0 | 0 | 0 | 1 | 0 |
| 3 | 4 | 0 | 2 | 1 | 3 | 1 | 0 |
| 4 | 0 | 2 | 4 | 2 | 1 | 1 | 0 |

The [Lean lemmas](../../../GUT/SU6/SelectionRules/Models/CyclicPatternOrbits.lean)
prove common rescaling of both selected charges, preservation of the two
pattern tests by nonzero rescaling, and normalized qque charge equal to one.
The exact orbit cardinalities remain computational checks.

## SU(6) filter

For the prior pointwise scalar/block action on the fifteen, write phases as
`Q=a+c+w`, `U=a+2c`, `E=a+2w`. Their qque charge is identically zero.
`no_scalar_block_fit` proves that any nonzero-qque assignment in this family
cannot satisfy those three formulas. The proof needs no determinant or
homomorphic-lift premise and therefore also excludes fits after enforcing them.
The script separately enumerates all 125 determinant-compatible Z5 phase
quadruples `(a,c,w,t)` with `3c+2w+t=0`. Each representative has zero fits;
a neutral phase assignment is a positive fitting control.

This filters a specified SU(6) realization, not all possible embeddings,
non-Abelian actions or changed light placements. It supplies no mass/light
model certificate or anomaly cancellation. Twenty charge candidates have
been reduced to five generator representatives, and all five require
escaping the already proved standard scalar/block class.

## Separate hypercharge dressing observation

A further explicitly distinguished operation adds s times the integer
hypercharge vector `6Y=(1,-4,2,-3,6,3)` to every species charge, modulo five.
On the parameters this is `(x,y,h) -> (x+s,y-3s,h+3s)`.
`hypercharge_dressing` proves both selected charges unchanged. The finite
check shows the five normalized representatives are connected by this
operation, so at the level of the supplied charge equations there is one
family modulo generator change and hypercharge dressing.

This does not certify an equivalence between unspecified UV models or
transport every actual quotient action. Interpreting dressing as physically
invisible additionally uses a genuine compatible gauge action and its local
invariant/coinvariant dictionary. Those application inputs are not silently
supplied here. Adding hypercharge cannot repair the scalar/block fit, since
it preserves the nonzero qque charge.

## Endpoint

The quotient makes the charge search substantially smaller but produces no
new protecting SU(6) model. The remaining issue is realizing this charge
family with a different actual placement/action. Repeating the previous
scalar/block fit for the other nineteen representatives is unnecessary.
No broader UV classification, physical allowance, all-degree B1 certificate,
rate calculation, merge or push is included.
