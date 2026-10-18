# SU(5) Scalar/Block Physical Qque And Mass Controls

## Statement And Inputs

[GUT.SU5.ScalarBlockQque](../../../../../GUT/SU5/SelectionRules/ScalarBlockQque.lean)
uses actual `Ten × BarFive`, where Ten is the second exterior power of the
fundamental five. Input: finite Abelian H, genuine complex-linear unitary U,
pointwise diagonal SU(5) lifts `diag(c I3,w I2)` and scalar a/b compensation.
The Hermitian form is transported from the existing unitary representations.
No homomorphic lift, UV commutation or auxiliary-factor group law is assumed.

The standard SM embedding and branching derive the actions on actual embedded
Q, uc, ec as `a c w`, `a c^2`, `a w^2`. The field group law derives their
characters. The physical qque phase cancels using dual right-handed uc/ec.
SM commutation and the joint representation are derived. Range coordinate maps
identify the genuine SM/H action with actual field restrictions.

`exists_actual_exterior` gives a nonzero SM/H/SL(2,C)-invariant fermionic
exterior coefficient on those participating fields. It transports the existing
[physical qque construction](../Physics/LORENTZ_EXTERIOR_QQUE.md), whose named
unit-flavor witness is 2. H acts trivially on spinors. The d/L charge-helper
entries are unused placeholders, not a duql result.

## Mass And Actual Light Fields

Zero mass supplies the first inhabited light control. `LightMass` removes the
particular mass formula but supplies SM/H invariance and actual light
membership for the three embeddings. Joint invariance and radical stability
are derived; `exists_light_exterior` combines membership and nonvanishing.
No index condition replaces those certificates.

[ScalarBlockMassExtension](../../../../../GUT/SU5/SelectionRules/ScalarBlockMassExtension.lean)
adds a ten/dual-ten pair with standard SM and trivial H action. Its orthogonal
evaluation mass has a complex scale c. Theorems prove nonzero mass for c != 0,
retention of the original light species, radical dimension 15 for c != 0
(and 35 for c = 0), and a surviving physical coefficient on the retained
participating fields. The extension has no supplied full-UV covariance,
UV Yukawa/scalar origin or arbitrary mixing classification.

## Additional Species-Dependent Mass Family

[MixedTenMass](../../../../../GUT/SU5/SelectionRules/MixedTenMass.lean)
uses two actual tens, one bar-five and one dual ten. Both tens share a genuine
scalar residual character chi; bar-five has an independent psi. An arbitrary
complex row per ten species gives a mass intertwiner, whose symmetric Dirac
form is SM/H invariant. Injective equivariant kernel maps are derived for every
row, including zero rows, and their actual ranges admit a nonzero physical
qque exterior coefficient. The three species need not use a common UV copy.
For three nonzero rows, the map is surjective, the mass nonzero and radical
dimension 15. Zero mass has radical dimension 35; partial rows retain further
zero modes. No full spectrum equivalence follows merely from a dimension.

See [mixed-mass result](../../../../topics/su5-matter-mass-protection/mixed-mass-result.md)
for controls, arbitrary-parameter scope and the affine splitting subset. The
shared chi restriction, trivial spinor action and no UV coupling-origin claim
remain explicit. This is not general compensated flavor mixing. The new
strict audit covers 95 declarations and rejects transitive SU(6) imports.

## Arbitrary-Copy Matrix Family

[MatrixTenMass](../../../../../GUT/SU5/SelectionRules/MatrixTenMass.lean)
uses p source tens, q dual-target tens and one untouched bar-five. Three
arbitrary complex species matrices define a genuine SM/H mass intertwiner.
For q < p, rank-nullity derives nonzero kernel vectors and actual injective
equivariant light species maps; their participating ranges have a nonzero
physical qque exterior coefficient. A supplied nonzero-kernel version works
at other sizes. There is no full-rank or shared-copy assumption. Common chi,
trivial spinor action and the species Dirac ansatz remain fixed. No arbitrary
invariant-mass classification or whole-light coefficient extension is asserted.
See [matrix result](../../../../topics/su5-matter-mass-protection/matrix-mass-result.md).

## Derived Normal Form And Non-Scalar Copies

[InvariantMassNormalForm](../../../../../GUT/SU5/SelectionRules/InvariantMassNormalForm.lean)
derives, for common scalar residual action, the exact species matrix/Dirac
normal form of every invariant symmetric mass on the current carrier. Same-side
Majorana candidates vanish by actual SM charge separation; Schur and the
actual branching classify the remaining entries. For p > q, physical light
coefficient existence follows for arbitrary such mass.

[NonScalarCopyMass](../../../../../GUT/SU5/SelectionRules/NonScalarCopyMass.lean)
uses actual `Ten tensor S + bar-five + (Ten tensor T)*`, genuine common copy
actions and three arbitrary equivariant species maps. Compact continuity and
target unitarity are explicit. Positive source-minus-target dimension derives
actual shared kernel splits, injective equivariant light species embeddings,
and physical exterior coefficients on their participating ranges.

The preceding normal-form result retains scalar action, and the non-scalar result
retains species-map input. The subsequent
[NonScalarInvariantMass](../../../../../GUT/SU5/SelectionRules/NonScalarInvariantMass.lean)
removes both together on the same non-scalar carrier. Finite-copy coordinate
bridges, actual SM Schur classification and tensor cancellation derive the three
residual-equivariant maps from arbitrary invariant symmetric B. Exact form equality
identifies radicals and yields actual participating-range physical qque nonzero
for positive dimension difference. See
[unified results](../../../../topics/su5-matter-mass-protection/unification-result.md).
The [connection ledger](../../../../topics/su5-matter-mass-protection/remaining-general-connections.md)
retains full-light, global descent and UV obligations.

The subsequent [target-unitarity removal](../../../../topics/su5-matter-mass-protection/target-unitarity-result.md)
proves the `_of_continuous` model endpoints without supplied target unitarity.
Compact continuity derives the internal unitary target; equivariant kernel
identifications transport its splits back to original participating ranges and
the same arbitrary input B. It does not assume the given metric is invariant.

The [algebraic continuation](../../../../topics/su5-matter-mass-protection/algebraic-copy-result.md)
adds `_of_semisimple` endpoints for arbitrary H, no group topology and no target
semisimplicity/unitarity. Source semisimplicity and positive dimension difference
supply actual common kernel splits by isotypic independence. The same arbitrary-B
normal form yields original light ranges and physical exterior nonzero.

The [pure-carrier continuation](../../../../topics/su5-matter-mass-protection/algebraic-carrier-result.md)
removes the algebraic model endpoint's norm/inner-product inputs. Structural mass,
branching, actual range and arbitrary-B constructions now use finite-dimensional
complex vector spaces; the retained analytic wrappers remain separately checked.

## Scope And Evidence

This is conditional coefficient existence, not a generated Wilson coefficient,
a decay rate or a universal SU(5)/simple-group theorem. A coefficient on the
participating species is not an untyped functional on all-left fields.
The same-ten scalar/block presentation is a sufficient source mechanism;
it is not proved necessary for coefficient existence.

The older [Georgi-Glashow result](GEORGI_GLASHOW_QQUE.md) already treats compact
UV-centralizer generation actions and zero mass; it is not reproved here.
[Topic results](../../../../topics/su5-matter-mass-protection/results.md)
separately record the bounded mass and mixing assessment. Its exact finite
scripts are supplementary checks, not theorem premises or Lean mixed-model
instances. Further group applications and general residual flavor actions are deferred.

[Strict audit](../../../../../GUT/SU5/Audit/AuditScalarBlockQque.lean):
73 transitive declaration checks, standard three axioms only, and rejection of
SU(6) imports. [Verification](../../../../topics/su5-matter-mass-protection/verification.md)
records focused/full builds and exact controls at stage 01. No literature
premise is introduced; branching and coefficient dependencies are repository
proofs and standard library infrastructure.

## Shared Physical Implication

[PhysicalCommonCopyModel](../../../../../Physics/FieldTheory/Mass/PhysicalCommonCopyModel.lean)
abstracts the actual mass-square, range-action and physical exterior implication
without a SU(5) carrier or model-layer imports. Its model interface derives the
three full-copy mass squares for every invariant symmetric B; light support and
nonzero qque are conclusions under source semisimplicity and dim S > dim T.
[PhysicalCommonCopyAdapter](../../../../../GUT/SU5/SelectionRules/PhysicalCommonCopyAdapter.lean)
proves this interface from the existing SU(5) branching and arbitrary-B normal
form and calls the shared theorem directly. The SU(5) classification remains
model-specific; another matter model must prove its own realization.
See [the shared result](../../../../topics/su5-matter-mass-protection/model-independent-result.md).
