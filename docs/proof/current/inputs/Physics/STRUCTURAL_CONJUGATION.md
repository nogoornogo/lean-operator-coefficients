# Structural Conjugation Criterion

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: **LEAN-CHECKED**, conditional on actual conjugation witnesses and the
specified finite-dimensional matter/mass/target data.
The [original topic](../../../../topics/structural-conjugation/README.md) records the
first endpoint; the [assumption-relaxation topic](../../../../topics/conjugation-assumption-relaxation/README.md)
records independent totals and restricted unitarity. The
[partial-target topic](../../../../topics/conjugation-partial-target/README.md) additionally
weakens the global dual target to SM-weight coefficient matching below.
The [two-conjugation refinement](TWO_CONJUGATIONS.md) removes the third
ambient witness while preserving both supported signatures under these inputs.

## 2. Inputs and conclusion

### Statement

Let T be the fixed determinant-one rank-four torus used for the normalized SM
weights, G any group, and `j : T ->* G`. Suppose two elements of G implement
the coordinate permutations `(3 1)`, `(0 4)` (zero-based `Fin 5`):

```text
j (permute p t) = n_p * j t * inverse n_p   for every t in T.
```

Take an actual finite-dimensional complex representation of `G x H`, where H
is any Abelian residual group. Require only its restriction to `T x H` to be
unitary for the chosen inner product, and equip that restriction with an
invariant symmetric bilinear mass B. At each of the fifteen oriented SM weights,
and for every residual character q, require the actual radical's dual-index
coefficient to equal the corresponding finite nonnegative profile coefficient:

```text
n_rad(w_i, q) - n_rad(-w_i, -q) = P_species(i)(q).
```

Here `-q` denotes the inverse residual character, including for torsion charges.
Require the Q and down profiles each to have positive total; their totals need
not agree. No orbit profile equalities are assumed. Other weight coefficients
are not fixed by this matching condition. In particular, a global SM-plus-singlet
dual-character target is no longer required.

Then the charge profiles satisfy `Q = up = electron` and `down = lepton`.
There are supported residual-neutral `qque` and `duql` signatures, with actual
nonzero radical eigenvectors at all fifteen associated SM weights. In particular,
`ForbidsEverySupportedPhysicalDeltaBOneOperator` is false for the actual resolved
radical spectrum.

Finite Abelian H is included. No full Weyl-invariance certificate, desired
profile equalities, zero-mode support, or source Laurent polynomiality is an
input. B need only be invariant under `T x H`, not under G. The conjugating
elements are not assumed to preserve the radical or the inner product.

## 4. Proof structure

### Checked Derivation

1. Actual conjugation gives trace and dual-trace invariance for each permutation.
2. Conservation of the dual character under invariant symmetric mass identifies
   the radical dual trace with the source dual trace, without assuming that
   conjugation preserves the radical.
3. Faithful evaluation of finite sums of all actual scalar characters gives
   coefficient invariance. Restricting to integral SM-weight characters and
   using the local matching condition forces the charge-profile equalities.
4. Actual unitary mass-spectrum decomposition and local target positivity supply
   nonzero radical modes. The shared operator construction yields the signatures.

The first move also sends down weight 10 to lepton weight 13. Species-uniform
target profiles at all fifteen weights therefore replace the third move used
in the original proof; no third conjugator is inferred.

The general core is in Physics and imports no GUT application modules:

- [ConjugationSource](../../../../../Physics/StandardModel/Spectrum/Representations/ConjugationSource.lean):
  `TwoConjugations` and the retained `ThreeConjugations.toTwo` adapter.
- [TwoConjugationQque](../../../../../Physics/StandardModel/Spectrum/Representations/TwoConjugationQque.lean):
  the current two-witness full-support pair and obstruction; also a Q-only
  operator-local qque endpoint.
- [ConjugationDualIndex](../../../../../Physics/StandardModel/Spectrum/Representations/ConjugationDualIndex.lean):
  `coeff_permute` derives actual dual-index invariance without a target.
- [ConjugationPartialTarget](../../../../../Physics/StandardModel/Spectrum/Representations/ConjugationPartialTarget.lean):
  `Physics.ConjugationPartialTarget.HasPartialTarget`, `exists_actual_signature_pair`
  and `selection_rule_obstruction`; `of_full_target` recovers the old input.
- [RestrictedConjugationMassSource](../../../../../Physics/StandardModel/Spectrum/Mass/RestrictedConjugationMassSource.lean):
  the actual spectrum and retained full-target endpoint.
- [ConjugationMassSource](../../../../../Physics/StandardModel/Spectrum/Mass/ConjugationMassSource.lean):
  the retained ambient-unitary/common-total API wraps the weakened core;
  `spectrum_eq_restricted` identifies the actual resolved radical spectra.

### Checked Assumption Relaxations

The three earlier relaxations remain simultaneous; the new two-witness
theorem additionally replaces `ThreeConjugations` by `TwoConjugations`:

- Common positive species totals are replaced by positivity of the Q and down
  totals separately. Conjugation still derives equality within Q/up/electron
  and within down/lepton. Positivity then selects one occupied charge in each
  orbit. No equality between their totals is used.
- Ambient unitarity is replaced by restricted unitarity. Ambient trace and
  dual-trace conjugation invariance are algebraic. Unitarity enters only in
  the actual `T x H` radical's character/eigenvector decomposition.
- The complete SM-plus-singlet dual target is replaced by matching only at
  the fifteen oriented SM weights, for every residual character. The radical
  spectrum is still the actual one; a supplied formal polynomial is not a
  substitute. Its full support need not consist of integral torus weights.

The [partial-target controls](../../../../topics/conjugation-partial-target/results.md)
show that extra finite sectors whose dual contributions vanish at these weights
preserve matching. A coefficient example has nonzero exotic dual index and
matches locally but cannot match any full target with the same profiles and
arbitrary singlets. Conversely, vanishing of the added spectrum at positive SM
weights alone is insufficient: opposite-weight contributions also matter.
These are algebraic controls, not new ambient physical models. Other coefficients
remain constrained by the actual representation and conjugation identities;
the result does not permit assigning them arbitrarily in a model.

The [audits and verification](../../../../topics/conjugation-assumption-relaxation/results.md)
include a finite-residual coefficient example with totals 2 and 1, with no
possible common total. Its supported-neutral statement is checked. The actual
mass theorem accepts such a target conditionally, but this audit does not
construct an anomaly-consistent unequal-total matter model. Nor is a new
physical model with nonunitary ambient action exhibited. These are reductions
of sufficient hypotheses, not a claim that any retained assumption is necessary
or that dropping unitarity everywhere is valid.

### Positive And Negative Controls

[ConjugationAdapter](../../../../../GUT/Common/StandardChain/ConjugationAdapter.lean)
constructs the witnesses from signed SU(5) permutation matrices for every
supplied homomorphism `SU(5) -> G`. Its restricted representation, mass and
actual spectrum are definitionally the existing standard-chain data. It
recovers the endpoints for both algebraic and continuous model interfaces,
including an actual 15-dimensional finite-residual benchmark. Existing
SU(N)/Spin/candidate applications do not need new model assumptions.

[ConjugationTrialityObstruction](../../../../../Physics/StandardModel/Spectrum/Charges/ConjugationTrialityObstruction.lean)
shows that no ambient extension matching the actual 45-dimensional triality
source character can satisfy all three conjugations. Thus the earlier
[group-free counterexample](../../../../topics/group-independent-assumptions/spectrum-bridge.md)
is consistent with this sufficient criterion; torus embeddings alone are
not excluded. Its quantum anomalies remain outside the checked statement.
The new `TwoConjugationControls.triality_no_two` additionally excludes the two
witnesses for a unitary mass source matching that local light target.

## 6. Scope and limitations

### Scope And Generality

This is a sufficient structural criterion on a fixed SM weight-coordinate
model, not a classification of all GUT groups or SM embeddings. G need not
be compact, simple or topological in the algebraic core, and j need not be
injective. Existing continuous-chain adapters retain their stronger inputs.

The result generalizes the proof interface and recovers known SU(5) chains.
It does **not** yet demonstrate strictly wider physical model coverage,
necessity, minimality, or a new physical mechanism. Establishing any of those
is a separate task.

The conclusion concerns the existing dimension-six two-left/two-right
signature class. It does not assert a nonzero full-gauge/Lorentz/Grassmann
operator on arbitrary radicals, a generated Wilson coefficient, an amplitude,
or finite proton lifetime. The [E6 literature boundary](../GUT/E6_LITERATURE_BOUNDARY.md)
is unchanged.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
