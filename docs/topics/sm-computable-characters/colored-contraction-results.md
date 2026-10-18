# Actual mixed-color contraction spanning

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. This implements the first two stages of
the [contraction plan](colored-contraction-plan.md). Original endpoint 2
remains open at restricted-factor nonvanishing and the all-content consumer.

## Proved comparison and spanning

`SL3ColorPlanes` constructs the three actual complex SL2 coordinate planes,
proves their compact compatibility with the existing SU3 planes, covers
every elementary transvection and invokes the pinned transvection-generation
theorem. Invariance on those planes therefore implies full SL3 invariance.

`SL2SpannedProducts` proves closure under direct products and constructs
algebraic dual-doublet equivalence. `SL3CompactComparison` identifies each
plane restriction of defining color with a doublet plus a scalar, constructs
the dual restriction and propagates symmetric-power spanning to arbitrary
mixed tensor powers. Every compact SU3-invariant functional on those actual
raw sources extends to complex SL3. No continuity, density or unformalized
unitary-trick premise is supplied at that endpoint.

`SL3TensorCommutant` normalizes an arbitrary complex GL3 matrix by a scalar
cube root of its nonzero determinant. Scalars act on an n-fold tensor as
their n-th power, so an SL3-commuting endomorphism also commutes with GL3.
Pinned TauCeti Schur-Weyl then expresses it as an actual permutation-algebra
action. `SL3DualTensorCommutant` proves the corresponding assertion for
contragredient powers by inverse transpose and the actual dual-coordinate
equivalence. It does not identify color with its dual as representations of
the same group action.

`TensorPowerDualEquivalence` equips mathlib's canonical perfect tensor
pairing with its group action and proves the semantic curry/evaluation law.
`SU3BalancedContractions.formula` consequently writes an arbitrary balanced
compact-color coefficient on pure tensors as a finite linear combination
of products of evaluations, indexed symbolically by permutations.

`TensorVolumeSplit` constructs the determinant coefficient and its actual
equivariant section by normalized antisymmetrization. The factorial
normalization and inverse law are proved for arbitrary degree; no tensor
basis is expanded. Tensoring these splits supplies arbitrary determinant
volume blocks and degree-raising retractions.

`TensorContractionSpan` derives contraction spanning from this split and
a proved permutation commutant. `SU3VolumeContractions.spanning` discharges
the defining-color instance for degrees `(q+3k,q)`;
`SU3MixedContractionSpan.dual_spanning` discharges the covector instance for
degrees `(q,q+3k)`, including actual bidual transport and compact restriction.
The existing triality theorem excludes the other raw degrees. Thus the
raw mixed-color spanning connection uses no new mathematical input.

`InvariantSpanningRestriction.allowed_iff` proves a reusable next step: on
an actual split source, support holds exactly when one member of the proved
finite invariant spanning family survives its source embedding. This is a
helper, not the final classification: its surviving-contraction tests still
need the positive diagram criterion from the plan.

## Boundary and next proof

The explicit contraction functionals and their spanning proofs are complete.
Their reduction to products of pairings/determinants on grouped symmetric
slots, trace/symmetry exclusions, simultaneous flag nonvanishing, bounded
incidence data and the final all-content q/l consumer remain to be connected.
No new literature premise, Weyl reduction, numerical rank/multiplicity
certificate, dependency change or proof-limit increase is used here.

See [verification](colored-contraction-verification.md).
