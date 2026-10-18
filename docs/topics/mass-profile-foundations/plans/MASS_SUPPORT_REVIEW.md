# Mass support and nonzero-mass review

Archived checkpoint; not a current work queue. Consult the current topic records.

Reviewed commit: `checkpoint 01`, against `checkpoint 02`.

## Support bridge review

The new `StandardWeylSupportedOperator` and its persistent audit type-check.
The audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The conditional theorems are retained.

They do **not** complete the intended zero-mode bridge:

- `pUV` is the ultraviolet source character, not the radical character.
- `nonzeroOrbitProfiles` assumes two UV coefficients are nonzero; it does
  not derive support from the radical's dual-SM target.
- `generations_ne` permits both signs. A nonzero antisymmetric coefficient
  alone does not imply support in its specified orientation.
- The audit's examples still assume `hOrbit` and do not construct a
  zero-mode witness.

The former ACTIVE completion claim has been corrected. No checked lemma is
discarded, and the existing scoped Dirac theorem is unchanged.

## Nonzero-mass proposal review

The uncommitted proposal is not a bilinear mass construction: conjugating
a Hermitian form makes it linear in one argument and conjugate-linear in
the other, not complex-bilinear in both. Its projections also assume a raw
product layout that the charge-sector-refined canonical fields do not have.
The file contains placeholders and is not trusted.

The subsequent impossibility argument does not apply to this model:

1. The model's mass is invariant under `CombinedGroup H`, the fixed physical
   compact four-torus times the residual group, not the whole UV SU(6).
   An obstruction requiring the latter is insufficient for the former.
2. The SU(6) exterior square `15` is not self-dual or quaternionic. Its dual
   is the conjugate exterior square. The proposed self-duality reasoning is
   incorrect independently of the invariance-group mismatch.
3. On the standard SU(5) restriction, `15` contains `10 + 5`, while each
   `bar6` contains `bar5 + 1`. Thus the appropriate candidate pairs a `5`
   with one `bar5`, not the two `bar6` copies with each other. Neutral
   singlets also permit symmetric masses after restriction.

The branching identities already checked in `ConcreteSU6Branching` support
the restricted-character calculation. No full-SM zero-mode or nonzero
decay-amplitude claim follows from this review.

## Checked follow-up

`AbelianActualSpectrum` constructs actual nonnegative multiplicities, proves
faithful trace evaluation, and derives nonzero eigenvectors from nonzero
coefficients. `WeylZeroModeSupport` applies this to the actual mass radical:
positive generation index supplies every oriented SM weight/charge sector
and supported `qque`/`duql` witnesses, with no UV orbit-support assumption.
Negative index supplies the conjugate zero modes, not the oriented ones.

`ConcreteWeylNonzeroMass` replaces the discarded attempt with an actual
rank-one symmetric mass on the same matter and derives radical dimension
26. Its `not_all_symmetric_masses_zero` is a checked counterexample to the
proposed uniqueness statement. It uses `InvariantLineMass`, multiplying
two complex-linear functionals; it does not mistake a Hermitian form for a
complex-bilinear form. Lifting all extra modes to leave dimension 15 is
still an open benchmark strengthening.

`AuditWeylZeroModeSupport` checks these endpoints with only `propext`,
`Classical.choice`, and `Quot.sound`, and constructs finite-Abelian examples
without support hypotheses. The full scoped theorem retains its Dirac scope.

The discarded uncommitted proposal and three planning notes were preserved
temporarily under `.local-backup/stage 01-kilo-review/`. The user approved
deleting that untracked backup at stage 02; it is no longer available from
the working tree or recoverable from Git. It was not needed to clone, build,
or audit the repository. See the
[cleanup record](../../../architecture/WORKFLOW.md).
