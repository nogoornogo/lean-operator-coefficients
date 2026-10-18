# Uniform local L and conjugate-L multiplicities

The structural endpoint for constant L and conjugate-L contents is proved.
All fermion degrees n, Higgs weak degrees m and hypercharge indices delta
remain symbolic. The theorem uses three flavors and the existing actual
statistical exterior source. Supplied residual flavor actions are arbitrary;
local invariance evaluates their group element at the identity. Residual
selection, mixed contents and Q/color branching remain separate.

## Finite formula and support

Label the 12 field basis slots by (weak index, Weyl index, flavor), with
weak/Weyl weights independently +1 or -1 and three flavor copies.
For an n-element subset S and j in {0,...,m}, set

    p(S,j) = sum_{i in S} weakWeight(i) + 2*j - m
    q(S,j) = sum_{i in S} spinWeight(i).

Define A(k)=1 for k=0, A(k)=-1/2 for |k|=2, and A(k)=0 otherwise. Then

    M(n,m) = sum_{|S|=n} sum_{j=0}^m A(p(S,j))*A(q(S,j)).

The Lean definition stores the equivalent finite symmetric-weight coefficients:
normalization(k) is 1 at zero and 1/2 otherwise, and contributions are placed
at (|p|,|q|). `multiplicity` extracts c00-c02-c20+c22. Thus the formula is a
finite subset/weight sum, not an unevaluated kernel dimension or an exhaustive
dispatch on degrees. Although represented as a complex scalar, its equality
with the complex-cast kernel dimension proves its integrality and
nonnegativity on every neutral constituent.

[SMLKernelDimension](../../../Physics/StandardModel/Operators/SMLKernelDimension.lean)
proves:

- `kernel_dimension`: if delta=n, the actual finite kernel dimension is M(n,m).
- `rank_add_multiplicity`: rank + M(n,m) = choose(12,n)*(m+1).
- `allowed_iff`: local L coefficients exist iff delta=n and M(n,m) is nonzero.
- `multiplicity_llhh`: M(2,2)=6, using the independent LLHH coefficient basis.
- `multiplicity_odd` and `multiplicity_above_capacity`: the formula vanishes at
  odd fermion degree and beyond the exterior capacity 12.

[SMLConjugateMultiplicity](../../../Physics/StandardModel/Operators/SMLConjugateMultiplicity.lean)
proves a full local coefficient-space equivalence from conjugate L at delta
to L at -delta. Hence its support is delta=-n and M(n,m) nonzero, and its
neutral kernel dimension is the same M(n,m). The transport uses existing
`BnvLocalConjugation`, weak epsilon duality and special-unitary coordinate
duality. It neither conjugates nor identifies residual flavor representations.

## Proven character-to-kernel chain

[SMLWeightExpansion](../../../Physics/StandardModel/Operators/SMLWeightExpansion.lean)
connects the actual exterior/Higgs character to the signed-weight sum indexed
by S and j. [SMLContinuousCharacter](../../../Physics/StandardModel/Operators/SMLContinuousCharacter.lean)
constructs finite analytic copies, proves field-coordinate and arbitrary
exterior-source continuity, and identifies the actual coefficient dimension.
No continuity or multiplicity premise is left on this actual L family.

`SU2CoefficientExtraction` proves that compact Hom integration counts invariant
coefficients, with inversion invariance of Haar measure retained. For two
independent SU2 factors, Haar probability on the product equals the product
of the factor measures; Fubini connects the Hom integral to the already
proved iterated extraction functional. `SU2SignedWeights` averages the four
Weyl-reflected finite expansions and normalizes nonzero signed pairs.
`ExteriorContinuity` handles any exterior degree by continuous multilinear
orbits and their span. `SL2SpanContinuity` separately proves compact continuity
from symmetric-power spanning, without assuming analytic regularity of an
arbitrary SL2 action.

The final local connection retains color triviality and the exact hypercharge
neutrality condition. It uses the previously proved compact/full Weyl
coefficient comparison and actual finite-kernel equivalence. No literature
result is imported as an axiom or numerical theorem premise.

## Checks and remaining A2 gate

Strict audits: `AuditLeptonCounting` and `AuditSMLMultiplicity`. See
[verification](verification.md). The bounded exact rational diagnostic
[check-lepton-weights.py](../../../tools/exact-rank/check-lepton-weights.py)
checks zero/top exterior degrees, parity, integral nonnegative results and
LLHH over 169 degree pairs. Its output is diagnostic; it is not a Lean
certificate. The existing partial rank CSV and executable `evaluate` were
not changed, so their 107 unresolved numerical rows remain labeled unresolved.
Eleven of those rows now fall within the proved L/conjugate-L structural
formula; 96 Q/conjugate-Q rows still need color extraction.

At the L checkpoint the recorded A2 stop gate applied. The exact missing
Route A interface is a
proved SU3 color singlet extraction from a genuine finite two-dimensional
color-lattice character expansion, compatible with the actual Q exterior
source and its independent weak/Weyl factors. A proposed form is constant
term against the one-sided positive-root denominator for A2. The existing
`Sl3HighestWeightExistence` supplies a highest vector, not this dimension
formula. The pinned TauCeti Weyl-module `Character` and `SchurWeyl` files
supply GL characters/tensor-power identities, not the required Q exterior
branching or SU3 Haar-to-torus adapter. Proceeding would require a separately
frozen A2 proof program or a feasible uniform reduced-matrix alternative,
as required by the [accepted plan](neutral-literature-plan.md). The user
subsequently authorized continuing through either route; the
[Q/conjugate-Q result](q-gaussian-results.md) now completes the constant-Q
endpoint by the exact-coordinate variant of Route B.

This endpoint classifies constant L/conjugate-L local support. It does not
complete all-species support, q/l residual selection, the 572 assignments,
interactions, matching coefficients or rates.
