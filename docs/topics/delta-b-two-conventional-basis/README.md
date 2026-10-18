# Delta-B = 2 conventional basis and normalization

- ID: delta-b-two-conventional-basis
- Status: completed
- Result type: proved, with explicit spinor and generator-order conventions
- Working branch: `proof/delta-b-two-conventional-basis`
- Integration target: `master`; merge requires separate user direction

## Endpoint and frozen scope

Connect the proved one-generation, derivative-free all-right degree `(2,4)`
sector to conventional AAS/SSS contractions. Prove an explicit invertible
change of basis and coefficient extraction from the existing two probes.
Formalize the normalization bridge, not just a tensor-pattern identification.
No new flavor/chirality sector, RGE, matching, rates or matrix elements.
Dependency pins and the axiom boundary remain unchanged.

## Plan and acceptance

1. Construct the conventional ordered O1/O2/O3 multilinear maps on actual
   quarks; prove their pure-input formulas and invariance. Descend to the
   intrinsic sector and prove agreement with the existing block alternation.
2. Evaluate two probes of O3 and an SSS representative, prove the determinant
   is nonzero, and expose a linear equivalence with explicit inverse. Derive
   the O1/O2/O3 Fierz relation on the sector and a Q1/Q4 convention adapter.
3. Specify explicit four-component Euclidean charge-conjugation/projector
   matrices and the right-Weyl embedding. Verify their algebraic conventions
   and prove the bilinear reduces to the repository's epsilon pairing.
4. Relate unnormalized alternation, normalized multilinear coefficients and
   Grassmann monomial coefficients, including species factorials and the
   interleaved-slot sign. Do not assert a numerical literature normalization
   without this bridge. Any convention dependence must remain explicit.
5. Persist strict transitive axiom audits; run focused builds, full `lake
   build`, layout/link checks and `git diff --check`; review and commit.

If a new foundational Grassmann interface is required beyond the existing
exterior-algebra APIs, freeze that missing interface and seek a scope decision;
do not silently replace normalization by an assumption.

## Result and boundaries

Branch created from clean `master`. Existing two-coordinate equivalence and
block Fierz relation are the proved inputs.

- Implemented the actual O1/O2/O3 ordered multilinear maps, their pure-input
  formulas, independent color/Weyl invariance and intrinsic exterior descent.
  O3's descent equals the existing existence-pilot coefficient, not just its
  value on a probe; the old unnormalized witness `24` is preserved.
- Implemented an explicit Hermitian Euclidean gamma representation, Clifford
  relations, `C = gamma2 gamma4`, charge-conjugation identities, projector
  idempotence and the right-Weyl bilinear reduction. The adapter fixes
  `gamma5 = -(gamma1 gamma2 gamma3 gamma4)` and the first block as right-handed.
  This is an explicit convention, not a proof of equality with an unspecified
  published gamma matrix basis.
- Proved a bijective, sign-preserving enumeration of the 48 species
  permutations and its agreement with full six-slot alternatization.
  `O1_block`, `O2_block`, `O3_block` identify actual decomposable-quark exterior
  evaluations with the existing block alternation for arbitrary inputs.
- Proved the unnormalized O1/O2/O3 probe columns `(0,48)`, `(48,-12)`,
  `(16,-20)` in Lean, and the O3/O2 determinant `768`. The linear equivalences
  `conventionalEquiv` and `chiralEquiv` include both inverse identities.
  The intrinsic sector obeys `O2 - O1 = 3 O3`.
- Constructed explicit Grassmann polynomials as sums of ordered coordinate
  generator wedges. Their standard determinant pairing equals full
  unnormalized alternatization. Sorted monomial coefficients equal exterior
  basis evaluations; the polynomial is independent of the coordinate basis.
  The actual Grassmann polynomials inherit both two-coefficient reconstructions.
- Connected each O1/O2/O3 pure-input formula to the explicit four-component
  `C P_R` diquarks. This uses the checked Euclidean convention above, not an
  unspecified gamma representation or a renormalized-operator premise.

All frozen endpoint obligations are closed. The user authorized integration
at stage 01; see [the integration record](../delta-b-two-model-interface/integration.md).
Other flavor/chirality sectors and physical matching,
RGE, matrix elements and rates remain outside this topic.

## Coefficients and normalization

For the existing interleaved probes `t0,t1`, the coefficients in
`alpha O3 + beta O2` are

`alpha = -t0/64 - t1/16`, `beta = 5 t0/192 + t1/48`.

With `Q1 = -4 O3` and `Q4 = -(4/5) O1 - (16/5) O2`, the coefficients in
`a Q1 + b Q4` are `a = t1/80`, `b = -(5 t0 + 4 t1)/768`.

No factorial is built into Grassmann generator multiplication or the
determinant pairing. For an **admissible species-alternating** ordered
coefficient, its raw polynomial is `48` times the polynomial of the existing
normalized `liftCoefficient`, with `48 = 2! 4!`, not `6!`.
The conventional ordered Oi maps need not themselves be species-alternating;
their raw polynomials correspond to `descend Oi`, without a `1/48` factor.
Changing from interleaved `u,d,u,d,d,d` to species-block `u,u,d,d,d,d` gives
one minus sign. Consequently interleaved probe values must not be identified
with sorted block-order monomial coefficients without that sign.

## References

- [Intrinsic classification](../delta-b-two-completeness/README.md)
- [Historical convention boundary](../delta-b-two/feasibility.md)
- [Two-coordinate source](../../../Physics/StandardModel/Operators/SixQuarkTwoCoordinates.lean)
- [Contraction relations](../../../Physics/StandardModel/Operators/DeltaBTwoContractionRelations.lean)
- [Conventional operators](../../../Physics/StandardModel/Operators/SixQuarkConventionalBasis.lean)
- [Conventional coordinate inverse](../../../Physics/StandardModel/Operators/SixQuarkConventionalCoordinates.lean)
- [Species permutation bridge](../../../Math/RepresentationTheory/SixSlotSpeciesSum.lean)
- [Grassmann polynomial and pairing](../../../Math/LinearAlgebra/GrassmannCoefficient.lean)
- [Physical normalization bridge](../../../Physics/StandardModel/Operators/SixQuarkGrassmannNormalization.lean)
- [Explicit spinor convention](../../../Physics/FieldTheory/Spinor/RightWeylChargeConjugation.lean)
- [Exact regression](../../../tools/delta-b-two/conventional-probes.py)
- [Rinaldi et al., Sec. II.1, equations (1)-(8)](https://arxiv.org/html/1901.07519#S2.SS1)

The source fixes color contractions, `C = gamma2 gamma4`, chiral projectors,
and conventional-to-chiral operator combinations. Its renormalized-operator
claims are not premises here. A concrete spinor matrix representation must
be stated and checked rather than inferred from the displayed C identity.

## Verification

- Full `lake build` passes (5958 jobs), including the focused conventional
  and species/Grassmann audits. Persisted strict transitive checks cover
  53 physics declarations and 12 generic mathematical declarations, allowing
  only `propext`, `Classical.choice` and `Quot.sound`. New sources have no
  residual warnings; existing dependency warnings are unchanged.
- `python3 tools/delta-b-two/conventional-probes.py` passes; this is a
  computational regression and not a spanning/normalization premise.
- Layout checks pass for 905 modules. Local links and `git diff --check` pass.
- The fixed gamma Clifford table has a local 800000-heartbeat bound. It checks
  sixteen pairs of four explicit 4-by-4 matrices; no invariant-classification
  resource limit or dependency pin was changed.

The new classification, enumeration and normalization proofs use the default
heartbeat limit; no resource increase, dependency change or audit exception
was added. The earlier construction checkpoint is commit `checkpoint 01`.
