# Historical GUT Assumptions

These independently scoped results are not premises of the current general
completeness theorem. Archiving changes neither their statements nor their
recorded verification. Retain external premises and application limits.

### Retained Ledger Context

Updated: stage 01.

Specified unified groups, embeddings, matter, vacua and model adapters live here. Their hypotheses do not automatically transfer to the weaker shared physics interfaces.

See the [cross-domain index](../../../../ASSUMPTIONS.md), [Math ledger](../../Math/ASSUMPTIONS.md), [Physics ledger](../../Physics/ASSUMPTIONS.md) and [GUT ledger](../ASSUMPTIONS.md). These ledgers distinguish required inputs, derived properties, external theorem inputs and exclusions in their individual statements. No uniform hypothesis package is imposed.

## Specified SU(6) Yukawa Spectra

The [SU(6) family](../../../../../topics/yukawa-family-spectrum/README.md) uses the existing
unitary symmetric-form scalar, original full-SU(6) Yukawa tensor Y0 and
specified SM x H-fixed vacuum v0 on actual 27-dimensional matter. Residual H
is an arbitrary commutative group acting neutrally as in the original source.
Zero bare mass and Y=yY0, v=t v0 give the proved mass (y*t)B0. Nonzero product
gives the exact 15-dimensional SM radical as a representation; zero product
gives all 27 UV modes. No other couplings, vacuum minimization or physical
decay amplitude are covered by this spectrum assertion. The endomorphism
parameterization of all couplings does not supply a rank stratification for
all their vacuum evaluations. No external literature input was added.

The [independent-block family](../../../../../topics/yukawa-independent-blocks/README.md)
keeps the same scalar, matter, zero bare mass and fixed vacuum. Equivariant
projection onto the exterior-matter summand and its complement constructs two
full-SU(6)-invariant Yukawa tensors. Their generated mass is proved equal to
the two-block normal form, with independently recoverable coefficients and
a radical consisting of the original light representation plus scaled
Five/dual-Five and singlet-pair radicals. This gives 15, 17, 25 or 27 complex
zero modes and proves that two couplings in the family agree exactly when
both coefficients agree. The former concrete kernel timeout is avoided by
deriving complementary branching from linearity inside a generic lemma;
the equality is proved, not supplied as an axiom or physical input. A complete
basis of all allowed Yukawas and spectra for their other couplings remain
outside this milestone.

The [full-space coordinate checkpoint](../../../../../topics/yukawa-full-space/README.md)
computes a 22-dimensional Lie commutant and five-dimensional vacuum image
using exact external arithmetic. These numbers are not imported as theorem
premises. `SmallSymmetricRank` proves the kernel formula for an explicitly
defined block map and its possible dimensions 15, 16, 17, 25, 26, 27.
Transport of this block-kernel formula and the residual irreducible
decomposition of the actual generated masses are now proved.
The [direct realization](../../../../../topics/yukawa-full-space/direct-realization.md)
constructs an actual full-SU(6)-invariant Yukawa family with an injective
five-dimensional vacuum mass image, and proves every form in that image is
generated. The [finite-stabilizer upper bound](../../../../../topics/yukawa-full-space/stabilizer-upper-bound.md)
now proves the converse for EVERY allowed full-SU(6) coupling, independently
of the external calculation. Four diagonal phases and four signed swaps are
proved to preserve the actual vacuum; invariance and symmetry reduce any
evaluation to five measured entries. Thus the entire fixed-vacuum mass image
is exactly the realized five-dimensional subspace. The full coupling-space
dimension 22 and evaluation-kernel dimension 17 are still external results.
No scalar or vacuum has been changed, and no finite calculation is imported
as an unchecked premise.

The [actual light-space criterion](../../../../../topics/yukawa-full-space/light-equations.md)
now proves radical membership iff five sets of three linear equations and
two singlet equations vanish, and identifies the full radical with the
kernel of that constraint map on actual UV fields. The exhaustive image
theorem extends this criterion to every allowed Yukawa at the same vacuum.
No nonzero coefficient assumptions are imposed. An actual nonzero singlet
is proved light when all five coefficients are 1.
The [spectrum transport](../../../../../topics/yukawa-full-space/spectrum-transport.md)
now gives a bijective coordinate map and a linear equivalence of the entire
actual radical with the abstract block kernel. The dimension formula applies
to all coefficients, and the six-value dimension list to every allowed Y.
The singlet block has an equivariant embedding and retraction for the actual
SM x H action, and is identified with 0, 1 or 2 copies of the trivial
one-dimensional irreducible representation.
The [non-singlet decomposition](../../../../../topics/yukawa-full-space/non-singlet-decomposition.md)
now supplies actual equivariant equivalences of the entire radical with
ten plus dual-five plus k singlets if a or b is nonzero, and ten plus five
plus two dual-fives plus k singlets if a=b=0. Ten, five and dual-five are
split into explicit SM factors whose irreducibility is proved; k is the
existing 2-by-2 kernel dimension. `all_yukawa_decompositions` connects this
to every allowed full-SU(6) Yukawa at the specified vacuum. No decomposition,
genericity or nonzero coupling is assumed. H is still neutral as in the
original model; the scalar is still the nonminimal symmetric-form model.
The full 22-dimensional coupling-space classification, other vacua and
physical decay amplitudes are not established by these results.

The [coupling-kernel milestone](../../../../../topics/yukawa-full-space/coupling-kernel.md)
identifies the actual coupling space with ker(vacuum evaluation) times
complex five-space, via a proved linear section of the probe map. Every
coupling has a unique decomposition; quotient dimension 5 is proved.
The statement that the full dimension is 22 is proved equivalent to kernel
dimension 17, but neither dimension is assumed or established. An explicit
nonzero full-group invariant coupling evaluates to zero at the specified
vacuum and to 1 at another scalar input. This is an algebraic witness, not
a replacement vacuum or a field-redefinition redundancy claim.

## Model-Specific Adapters

Do not copy the core's weaker inputs into these retained structures without
a checked conversion; conversely their stronger inputs are not universal
assumptions of the core.

- **Retained SU(5) matter:** the [separate theorem](../../../applications/GUT/SU5_SELECTION_RULE.md)
  uses actual `n(10 + bar5)`, n > 0. It does not inherit the SU(6) mass-removal
  hypotheses. Family-dependent actions and [extracted charge profiles](../SU5_CHARGE_PROFILES.md)
  are supported within its own scope.
- **Georgi-Glashow exterior benchmark:** actual `n(10 + bar5)`, n > 0,
  zero symmetric mass, and a continuous homomorphism from compact H into the
  unitary SU(5) centralizer. No Abelian assumption is imposed. The compatible
  continuous SM action, exact spectrum, both target packages and shared/pairwise
  positive support are derived, followed by the nonzero actual qque exterior
  endpoint. One- and three-generation trivial-H controls are checked.
  No vacuum or Yukawa condition is claimed. [Scope](../../../applications/GUT/GEORGI_GLASHOW_QQUE.md).
- **SU(6) classification/profile model:** [ContinuousProfileModel](../../../../../../GUT/SU6/SelectionRules/Models/ContinuousProfileModel.lean)
  retains its continuous injective semisimple/hypercharge geometry, actual
  continuous-unitary SU(6) matter with nonnegative copy counts, strict unitary
  Abelian action, invariant symmetric mass, and global dual target with a
  common positive profile total and singlet index data. Hypercharge rigidity
  and profile equalities are derived. [Embedding differentiability](../../Math/EMBEDDING_CLASSIFICATION.md)
  is derived from continuity; the geometric inputs are not removed.
- **Standard SU(5) chain:** [the continuous adapter](../../../applications/GUT/interfaces/standard-su5-chain.md)
  adds an injective continuous SU(5) -> G map and continuous unitary source
  actions to its Abelian mass/target interface. [SU(N), N >= 5](../../../applications/GUT/interfaces/standard-su-n.md)
  and [compact Spin(10)](../../../applications/GUT/SPIN_STANDARD_CHAIN.md) construct specific inclusions;
  these are not classifications of all SM embeddings.
- **Examples:** [SU(7)](../../../applications/GUT/interfaces/standard-su-n.md), [half-spin 16](../../../applications/GUT/SPIN_HALF_SPIN.md)
  and [E6-candidate 27](../../../applications/GUT/E6_POSITIVE_TARGET.md) derive targets for concrete
  sources, not arbitrary matter. Their inhabited zero-mass benchmarks do
  not establish realistic masses. The E6 27's vectorlike pair cancels in
  the dual index, not in its full 27-dimensional zero-mass spectrum.
