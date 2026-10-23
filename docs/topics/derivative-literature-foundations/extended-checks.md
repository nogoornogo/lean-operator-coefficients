# Additional Input Verification Results

The [four-part contract](extended-checks-plan.md) supplements the earlier
derivative and nonderivative checkpoints. Published input definitions and
dependency pins are unchanged. All four items were executed; complete
positive-derivative literature bases remain a partial endpoint.

| Item | Verified result | Remaining boundary |
| --- | --- | --- |
| Actual symmetry | Left-Weyl epsilon mass and scalar-spectator Yukawa coefficients pass old/unified transport, normalization, exchange sign and inverse checks. One Weyl field with any number of scalar spectators is forbidden by the central minus identity. | Actual SL(2,C), neutral Lorentz scalar spectators, off-shell d=0; no SM gauge or interacting mass classification. |
| Presentation changes | Source quotient, coefficients, inverse and evaluation transport under an equivariant linear equivalence carrying the full relation module. Arbitrary source basis changes use the conjugated action. A concrete species swap and generator value pass. | A new presentation must transport the action and complete relations together. No arbitrary basis map is asserted to preserve a fixed untransported action. |
| Equation generators | Nonzero common rescaling and elementary invertible row recombination preserve full two-sided differential closure and EOM/IBP. Both are instantiated on the actual two-species free equation family. | Zero scaling and noninvertible removal of equations are excluded. |
| Small complete sectors | C1: every zero-derivative multidegree (r,s) has actual full-quotient image dimension 1; the entire (1,1), d=2 source has image dimension 0. Exact scripts also check explicit surviving representatives and complete finite spans. | Other positive-degree C1 counts and C2 positive-degree invariant counts lack the stated semantic bridges below. |
| Conjugation/reality | Real-coupling scalar conjugation preserves full EOM/IBP, squares to identity and commutes with actual Lorentz action. The full free zero-derivative image has Hermitian real dimension 1. Paired on-shell Weyl adjoint/involution, derivative/action and conjugated equation-descendant checks pass. | No Hermiticity theorem for arbitrary mixed interactions or spectator-coupled generated inputs. An independent conjugate coordinate pair has real dimension 2; this is not a Weyl-source basis count. |

## Actual Lorentz old/new control

[WeylNonDerivativeChecks](../../../Physics/FieldTheory/Jets/WeylNonDerivativeChecks.lean)
constructs the old invariant coefficient on
Lambda^2(Field(Fin 2)) tensor Sym^m(Field(Unit)). Its value is epsilon(v0,v1)
times the symmetric scalar product. Invariance uses the actual determinant-one
left Weyl action, not Unit symmetry. `unified m` imports it through the common
d=0 entry with the actual Lorentz direction representation. Its normalized
value is 1, exchange gives -1, and both m=0 mass and m=1 scalar Yukawa are
nonzero. The inverse returns the supplied old coefficient.

The negative control is n=1 with arbitrary m. The central minus identity
acts by -1 on this source, so every invariant coefficient is zero in both
interfaces. This is a test of a forbidden one-Weyl sector, not a claim about
an arbitrary gauge or flavor model.

## Changing presentations without changing values

[InputPresentation](../../../Math/RepresentationTheory/InputPresentation.lean)
requires the actual relation-map equality, not only seed membership. Its
`source` and `coefficients` equivalences preserve quotient evaluation for
every class. `reexpress` constructs the transported action and relations
for any invertible linear source map. `reexpress_evaluation` and `inverse`
check the forward/inverse operations. Existing source maps are untouched.

For equation generators, equality of their complex linear spans implies
equality of the complete differential closure. Nonzero scaling and an
elementary row addition are proved specializations, including all products,
derivative descendants and the unchanged linear IBP range. The
[two-species controls](../../../Math/RepresentationTheory/TwoSpeciesDerivativeChecks.lean)
instantiate both operations and check a field-species relabeling and arbitrary
transported source basis change on an actual global coefficient.

## Small-sector completeness and its limits

C1 is the two-real-scalar, one-direction free specialization of
[1507.07240v1 Eq. (3.11)](https://arxiv.org/pdf/1507.07240v1), inspected on
PDF p. 13. The new Lean source uses the unbounded ordinary jet algebra,
both second-derivative equations with their full differential ideal, and
all ordinary total derivatives. Its Unit group is the intended no-symmetry
one-dimensional example.

- At d=0, weighted monomial support proves completeness at every specified
  content (r,s). A global functional obtained by removing positive jets
  annihilates the full EOM/IBP relation module and detects the generator.
  `imageEquiv` has both inverse laws and proves dimension 1, including
  contents (1,1), (2,2) and the vacuum.
- At content (1,1), d=2, `Bilinear.classify` exhausts the entire actual
  homogeneous source: phi' chi', phi'' chi and phi chi''. EOM and IBP kill
  all three. `Bilinear.full_source_zero` and `image_dimension` prove the
  full image is zero, rather than assuming the three candidates span.
- At d=1, the actual IBP relation between phi' chi and phi chi' is proved.
  For the remaining positive-degree counts, the exact finite calculation
  gives (1,1,0) and (1,1,1) at contents (1,1) and (2,2). It also checks
  explicit surviving representatives complete each nonzero finite quotient.
  A Lean global separating functional/full-relation comparison for these
  remaining sources is not supplied by those finite rows.

C2 uses [1706.08520v1 Eq. (6.3)](https://arxiv.org/pdf/1706.08520v1), PDF p. 58,
with the representatives discussed on p. 59. The two named routes remain:

| Route | Evidence | Exact unresolved bridge |
| --- | --- | --- |
| Structural actual quotient | Complete d=0 Lorentz image; specified d=2 representative vanishes; K squared is actually invariant. | Complete invariant spanning at d=2,4 and a global EOM/IBP-annihilating separator detecting K squared. |
| Complete finite coordinates | Exhaustive source sizes 1/20/305; full finite EOM/IBP plus infinitesimal row ranks 0/20/304. Appending the literal phi^4 or K squared coordinate vector increases rank by 1 and completes the finite space. | Lean actual-source/relation transport and the infinitesimal-to-full-group bridge, including the paper's Euclidean versus repository Lorentz conventions. |

The strengthened scripts are exact rational diagnostics using the Python
standard library. They are retained and reproducible:

```sh
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
```

They find no disagreement with the selected paper coefficients. Neither
script output nor the paper's series is a Lean premise. In particular, the
new K squared finite witness does not prove its actual Lorentz quotient
class nonzero. These precise partial stops do not cancel the reality check.

## Hermiticity is an additional input condition

[PolynomialJetConjugation](../../../Math/Algebra/PolynomialJetConjugation.lean)
fixes jet labels and conjugates polynomial coefficients. It commutes with
ordinary derivatives. The generic
[semilinear descent](../../../Math/Algebra/SemilinearDifferentialRelations.lean)
preserves the full differential closure and linear divergence range when
its seed and product conditions hold.

[ScalarRealityChecks](../../../Physics/FieldTheory/Jets/ScalarRealityChecks.lean)
applies this to wave phi + lambda phi cubed with real lambda. Conjugation
sends the seed at lambda to that at conjugate lambda, so a nonreal coupling
does not silently receive a real-input interpretation. In the supported
input it descends, is involutive and commutes with the actual Lorentz action.
For every n, c times the free phi^n class is fixed exactly when Im(c)=0.
`realImage_iff`, `realImageEquiv` and `real_image_dimension` identify all
Hermitian classes in the complete zero-derivative image with a real line.

For paired Weyl fields, the existing source already imposes both conjugate
linear EOM families before exterior algebra and IBP. Persistent consumers
check its adjoint, action and derivative laws and the vanishing of a
conjugated raw equation descendant. No mixed Higgs interaction is added.
[HermitianCoefficientChecks](../../../Math/LinearAlgebra/HermitianCoefficientChecks.lean)
separately proves that an independent conjugate coordinate pair has fixed
coefficients (c,conjugate c), hence real dimension 2, while a self-adjoint
line has real dimension 1. Independence of actual paired Weyl operators is
not a premise proved by this coordinate control.

## Final boundary

The four checks close actual-symmetry compatibility, presentation transport,
the stated additional complete scalar sectors and supported reality laws.
Remaining positive-degree C1/C2 complete-basis claims are explicitly partial.
No regression or contradiction is found in the proved or exactly tested
scopes. No analytic action, full SMEFT basis, quantum equivalence or new
dependency is introduced. The [verification record](verification.md#additional-input-verification-gate)
owns the acceptance commands and results. No master merge is authorized.
