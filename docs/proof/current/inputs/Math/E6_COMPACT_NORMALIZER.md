# Closed Compact Matrix Normalizer

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

**E6-0g is complete at the matrix/topological-group level.** It constructs
an actual closed subgroup of SU(27) and identifies its all-time exponential
directions with the previously proved 78-dimensional real form. It does
not identify this entire subgroup with compact E6 or add a physical endpoint.

## 2. Inputs and conclusion

### Checked Statement

Let `k = compactMatrixLieAlgebra`, the ambient-matrix image of the actual
skew-Hermitian E6 real form constructed in
[E6-0e](E6_COMPACT_REAL_FORM.md) and [E6-0f](E6_MATRIX_NORMALIZER.md).
[CompactNormalizer](../../../../../Math/LieGroups/E6/Minuscule/CompactNormalizer.lean) defines

```text
N = {g in SU(27) | conjugation by g and by g^(-1) preserves k}.

X in k  <->  for every real t, exp(t X) is in the matrix image of N.
```

`compactNormalizer` is a subgroup, is closed, and is compact. The theorem
`mem_compactMatrix_iff_exp_mem_normalizer` proves the equivalence for every
complex 27-by-27 matrix X, without a supplied normalizer, tangent or group
realization certificate. `exp_compactRealForm_mem_normalizer` and
`exp_generator_mem_normalizer` specialize it to the original real form and
all eighteen compact generators.

## 4. Proof structure

### Reusable Proof

- [LieNormalizerExponential](../../../../../Math/LieGroups/Matrix/LieNormalizerExponential.lean):
  a closed invariant real submodule of a Banach algebra is preserved by the
  exponential of a continuous linear operator. The proof takes limits of
  partial sums. TauCeti's `exp_continuousCommutator_apply` identifies the
  exponential of the commutator operator with conjugation by `exp X`.
  Conversely, differentiating the conjugation curve at zero gives `[X,Y]`;
  closedness keeps the derivative in the submodule. Thus Lie normalization
  is equivalent to preservation by conjugation for all real times.
- [SpecialUnitaryExponentialCriterion](../../../../../Math/LieGroups/SpecialUnitary/SpecialUnitaryExponentialCriterion.lean):
  `exp(t X)` lies in SU(n) for every real t exactly when X is skew-Hermitian
  and traceless. Necessity is proved by differentiating the unitary identity
  and the determinant at zero. It reuses the checked determinant-exponential
  formula; a single determinant value is not enough.
- [MatrixLieGroupNormalizer](../../../../../Math/LieGroups/Matrix/MatrixLieGroupNormalizer.lean):
  constructs the subgroup for any real matrix Lie subalgebra. Closedness
  follows from continuity of conjugation and closedness of finite-dimensional
  subspaces; compactness is inherited from SU(n). Combining the two analytic
  results gives the exact normalizer/skew/trace criterion.
- E6 specialization uses `compactMatrix_mem_iff_normalizes_skew_trace_zero`
  from E6-0f. Its algebraic bound discharges all three matrix conditions.

## 6. Scope and limitations

### Scope and Next Gate

The exponential criterion is checked, not an asserted identification with
a manifold tangent space. No manifold structure on N, connectedness,
simple connectedness, global form, order-three center, or integrated D5
inclusion is proved here. In particular, a full normalizer must not simply
be renamed compact E6.

**[E6-0h](E6_IDENTITY_COMPONENT.md)** now retains this criterion on the
closed compact connected identity component. It also constructs a central
element of order 27 in the full normalizer, ruling out its identification
with a group whose center has exponent dividing three. The component's
own center/global form remains undetermined. **[E6-0i](E6_LOCAL_LOG.md)**
now proves local real-form logarithms and exact exponential generation of
the identity component. Subsequent **[E6-0n](E6_TANGENT_LIE_ALGEBRA.md)**
closes local charts, smooth group structure and geometric tangent Lie
comparison. General integration/global classification foundations still
require the existing cost review. M2 is advanced but
not closed; M3-M5 and the E6 physical endpoints remain open in the
[feasibility ledger](../../../../topics/e6-global-topology/decisions/E6_FEASIBILITY.md).

## 7. Sources and verification

### Verification

The persistent [audit](../../../../../Math/LieGroups/E6/Audit/AuditCompactNormalizer.lean),
imported by `GUT.lean`, checks 22 declarations against only `propext`,
`Classical.choice`, and `Quot.sound`. It instantiates compactness,
topological-group structure, real dimension, the exact equivalence, and
the generator exponentials without additional certificates.

A negative control constructs `X = (2 pi i) I`. Its time-one exponential
is the identity and belongs to N, but its nonzero trace excludes X from k.
Thus the all-real-parameter hypothesis cannot be weakened to time one.

Targeted: **3833 jobs / 22 reports**. Full: **5428 jobs / 2247 reports**
(2246 axiom lists and one axiom-free report). All five new Lean modules
are warning-free; pre-existing warnings in dependencies remain unchanged.
The ten tooling tests pass and remain outside the proof trust boundary.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactNormalizer
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

Disposable logs: `.lake/e6-0g-audit.log` and `.lake/e6-0g-full-build.log`.
All proof/audit sources are tracked; dependency pins are unchanged.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
