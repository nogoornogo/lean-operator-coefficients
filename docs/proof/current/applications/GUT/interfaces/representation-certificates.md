# Constructive representation certificates

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Constructive
representation and subquotient certificates realize analytic matter blocks and
supply checked flipped-character applications.

## 2. Inputs And Conclusion

Finite-dimensional continuous sources, chosen torus certificates and stable
coordinate subspaces enter the respective construction APIs.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Unitarization, exterior/dual functoriality and torus eigenbasis transport
preserve the character certificates used by the obstruction.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Concrete analytic matter blocks

- `ContinuousSU6Unitarization.model` averages a finite-dimensional jointly
  continuous SU(6) action over the full compact group. `modelEquiv` preserves
  the algebraic representation and therefore its character.
- `FiniteBasisHilbertization.Copy` supplies finite algebraic spaces with a
  Euclidean coordinate model. `continuous_iff_coords` is the continuity API.
- `ContinuousUnitaryConstructions` proves tensor-product continuity and
  unitarity in [the generic Math module](../../../../../../Math/RepresentationTheory/Unitary/ContinuousConstructions.lean).
  Its bundled `dual` and `dualEquiv` in the
  [SU6 adapter](../../../../../../GUT/SU6/Representations/ContinuousUnitaryConstructions.lean) realize algebraic dual actions
  continuously and unitarily; inverse-group matrix coefficients establish
  their continuity.
- `RepresentationExteriorEquiv.lean` proves that exterior powers and duals
  preserve equivalences of actual representations.
- `ConcreteSU6Representations.fundamentalWitness`,
  `antifundamentalWitness`, and `exteriorTwoWitness` instantiate the hypercharge character rigidity
  continuous-unitarizable interface for the original algebraic `6`, `bar6`,
  and `15`. The exterior continuity proof uses minors of the defining matrix.
- `exteriorTwo_finrank` and `antifundamental_finrank` prove dimensions 15 and
  6. `exteriorTwoTorusEigenbasis` and `antifundamentalTorusEigenbasis` transport
  the previously checked weight certificates to the analytic models.
- `AuditConcreteSU6Representations.lean` and
  `AuditContinuousSU6Unitarization.lean` check the standard axiom boundary.
  The initial full build passed in 4143 jobs. These results supply the matter
  blocks of the complete index-based `ConcreteDiracBenchmark.model`, whose
  mass sector is explicitly zero.
- `ConcreteSU6Branching.lean` computes the trace characters of the analytic
  `6`, `bar6`, and `15` on every actual diagonal SU(6) point. The wedge sum
  enumerates all fifteen pairs, with bijectivity checked in the kernel.
  `signed_character_standard` proves that the signed source reduces to the
  explicit ten antisymmetric weights plus five inverse-coordinate weights
  when the sixth coordinate is one. This is a character-level branching
  identity, not yet a complete physical-model certificate.
- `AuditConcreteSU6Branching.lean` reports only standard axioms.
- `ConcreteSU6PhysicalTarget.lean` completes the physical target match.
  `physicalDiagonalPoint_last` checks the neutral sixth coordinate at
  `(-2,3)`; `physicalDiagonalPoint_coords` and `smExponent_eq` identify the
  fundamental and SM weights. `signed_character_physical` uses the actual
  branching formula, and Fourier faithfulness yields
  `signedSource_integralCharacter` for the existing ambient Laurent model.
  `signedSource_resolvedCharacter` and `signedSource_coefficientSpectrum`
  retain uniform charges in any additive Abelian group, giving one SM
  generation and no net singlets. The actual physical-torus interface is
  supplied by `signedSource_isSMTargetCharacterEquivalent`. No mass map or
  complete zero-mode spectrum is asserted.
- `AuditConcreteSU6PhysicalTarget.lean` checks the axiom boundary and exercises
  a nonzero torsion charge in `ZMod 2` and neutral residual characters of any
  Abelian group. The full build at stage 01 passes in 4149 jobs, with only
  standard axioms for the new audited declarations.

#### Constructive representation certificates now checked

- `GUT.FundamentalRepresentation.torusEigenbasis`
  - proves directly that the standard basis of the defining six-dimensional
    actual `SU(6)` representation is an eigenbasis for the flipped diagonal
    torus.
- `GUT.FundamentalRepresentation.physicallyAdmissible`
  - packages the defining representation as a
    `PhysicallyAdmissibleSU6Representation`.
- `GUT.CertifiedConstructions.TorusEigenbasis.prod`
  - preserves the torus eigenbasis certificate under direct sums/products.
- `GUT.CertifiedConstructions.TorusEigenbasis.tensor`
  - preserves the certificate under tensor products; the Lean proof includes
    the Laurent monomial identity that added weights evaluate to multiplied
    eigenvalues.
- `GUT.CertifiedConstructions.TorusEigenbasis.exterior`
  - preserves the certificate under exterior powers; the wedge basis has
    weight equal to the finite sum of the selected weights.
- `GUT.CertifiedConstructions.TorusEigenbasis.dual`
  - preserves the certificate under duals, with negated weights.
- `GUT.CertifiedConstructions.TorusEigenbasis.coordinateSubrepresentationEigenbasis`
  - certifies stable coordinate subrepresentations spanned by selected torus
    eigenbasis vectors.
- `GUT.CertifiedConstructions.TorusEigenbasis.coordinateQuotientEigenbasis`
  - certifies the complementary eigenbasis on quotients by stable coordinate
    subspaces.
- `GUT.CertifiedConstructions.TensorGeneratedCoordinateSubrepresentationCertificate`
  and `TensorGeneratedCoordinateQuotientCertificate`
  - package an actual representation as isomorphic to a stable coordinate
    subrepresentation or coordinate quotient of a tensor/exterior-generated
    ambient representation, and produce its torus eigenbasis certificate.
- `GUT.CertifiedConstructions.TensorGeneratedSubquotientCertificate`
  and `TensorGeneratedSubquotientSU6Representation`
  - bundle the currently Lean-ready subquotient realization class used as the
    proxy for highest-weight algebraic representation constructions.
- `GUT.CertifiedConstructions.FiniteTensorGeneratedVirtualSU6Representation.normalizedPoly_swap36_fixed`
  - proves finite virtual sums of tensor-generated certified representations
    are fixed by `swap36` in the normalized Laurent model.
- `GUT.CertifiedConstructions.FiniteTensorGeneratedVirtualSU6Representation.no_flippedSM_uplift`
  - proves that no finite virtual tensor-generated certified representation
    has normalized polynomial equal to the flipped SM target.
- `GUT.CertifiedConstructions.FiniteTensorGeneratedSubquotientVirtualSU6Representation.normalizedPoly_swap36_fixed`
  - proves the same `swap36` fixedness for finite virtual sums of
    tensor/exterior-generated subquotient certificates.
- `GUT.CertifiedConstructions.FiniteTensorGeneratedSubquotientVirtualSU6Representation.no_flippedSM_uplift`
  - proves that no finite virtual tensor/exterior-generated subquotient
    certified representation has normalized polynomial equal to the flipped SM
    target.
- `GUT.AuditFlippedWeylObstruction`
  - collects explicit named Lean checks for the seven flipped critical audit critical audit
    points in the current `(3 6)`/normalized-coordinate-ring scope, including
    actual-torus faithfulness, preservation of the flipped torus, finite-virtual
    restricted-character invariance, explicit flipped-SM factorization,
    detection of non-invariance on the actual subtorus, consistency of
    `C`, `Cbar`, and `W` with the torus variables, and exclusion of arbitrary
    finite virtual restricted characters as actual-torus functions, without a
    Laurent-provider hypothesis.  It also records the provider-modeled and
    tensor-generated subquotient variants, plus the fully instantiated
    physical `U(3) x SU(2)` target and its concrete character-image exclusion.

## 6. Scope And Limitations

Certificate-based subquotient realizations are not a classification of every
representation; character branching is distinct from full light-spectrum
identification.

## 7. Sources And Verification

The [scope dossier](../FLIPPED_WEYL_OBSTRUCTION.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
