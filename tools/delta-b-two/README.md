# Exact species-quotient certificates

Run `python3 tools/delta-b-two/species-quotient.py` to reproduce the four
color and Weyl permutation matrices, the rank-23 rational system, its two
kernel vectors, and sparse row certificates. Only Python's standard library
and exact `Fraction` arithmetic are used; no simulation or dependency update
is involved.

`--lean-proof` prints the isolated `kernel_reconstruct` proof;
`--lean-words` prints the 48 generator words for the species subgroup.
Both modes write only to standard output. They are development helpers, not
trusted oracles or prerequisites of a Lean build.

The maintained Lean source separately proves the permutation identities on
arbitrary vectors, verifies every rational row deduction with
`linear_combination`, and checks coverage of the subgroup with
`decide +kernel`. No rank result from this script is used as a premise.

## Conventional contractions

Run `python3 tools/delta-b-two/conventional-probes.py` for the exact
unnormalized O1/O2/O3 probe columns, the O3/O2 inverse and all 225
degree-`(2,4)` Grassmann basis monomial Fierz controls. It also checks the
displayed Q1/Q4 conventional combinations. Only integer and rational
standard-library arithmetic is used.

The [conventional-basis topic](../../docs/topics/delta-b-two-conventional-basis/README.md)
now proves the probe inverse and the ordered-polynomial/exterior-descent
bridge in Lean independently of this script. Sorted species-block monomial
coefficients carry the minus sign for changing from the interleaved probe
order. This script remains a regression, not a normalization premise or proof oracle.
