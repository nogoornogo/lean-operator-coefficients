# Nonderivative Inputs Through The Integrated Interface

All Z1–Z5 cases in the [bounded contract](nonderivative-recheck-plan.md)
are proved. Old nonderivative coefficients are actual inputs to the new
zero-degree entry, with inverse maps and unchanged evaluation. Separate
model tests use nonderivative representatives in the full EOM entry.
This distinction matters: compatibility of the off-shell input does not
assert that adding interaction equations preserves its allowed values.

The persistent sources are
[NonDerivativeInputChecks](../../../Math/RepresentationTheory/NonDerivativeInputChecks.lean)
and [NonDerivativeModelChecks](../../../Physics/FieldTheory/Jets/NonDerivativeModelChecks.lean).
Their strict audits and complete build are recorded in
[verification](verification.md#nonderivative-input-recheck-gate).
Published input definitions, signatures and dependency pins are unchanged.

| Case | Supplied input | Proved check |
| --- | --- | --- |
| Z1 | Original exterior/symmetric invariant coefficient, arbitrary component labels, group and counts | Both round trips; forward/inverse evaluation; zero-degree IBP is bottom; nonzero/forbidden agreement; independence of direction action |
| Z2 | Explicit determinant coefficient on two odd components and product coefficient on one even component | Pure Bose, pure Fermi, mixed and vacuum nonzero values; odd swap gives -1, repeated odd component gives 0; Bose permutations preserve evaluation |
| Z3 | Original finite-local/statistical coefficient with complete scalar local basis | Empty extra relations recover the original input; source and computed-coordinate evaluations agree; inverse coefficient reconstruction |
| Z4 | Actual Lorentz scalar full EOM input, evaluated on phi^n | Every free nonderivative power has arbitrary coefficient value and a one-dimensional actual selected image; interacting cubic values satisfy exactly lambda*c=0 |
| Z5 | Span of rho squared and rho cubed in the actual generated Higgs input | Global SM/Lorentz stability; restriction/extraction on both powers; actual full-quotient image equivalence; coefficient inverse and generated/direct agreement |

## Z1 — Use An Existing Coefficient As The Input

`Math.NonDerivativeInputChecks.Bridge` uses the original source
Lambda^n(Field F) tensor Sym^m(Field B), including zero field counts.
`toUnified` consumes its existing invariant coefficient through
`DerivativeInterface.fromNonDerivative`. The target is exactly
`DerivativeInterface.graded rhoF rhoB sigma n m 0`, with no new relation
or caller proof. It is a typed usage wrapper in the checks, not a changed
public factory.

The tests prove both inverse laws and evaluation on every original source
element, not only basis examples. They also preserve nonzero and universal
vanishing, and compare the result for any two supplied direction actions.
Thus even a nontrivial symmetry action on derivative directions introduces
no zero-degree constraint. Component sets and the symmetry group are
arbitrary; only the existing finite direction-index hypothesis is used.

## Z2 — Concrete Statistics Inputs

`Statistics.oldBose m` and `oldMixed m` are constructed in the original
input type before conversion. The latter uses the actual exterior-square
determinant, while the even part uses the actual symmetric-power product.
`bose` and `mixed` then import them through the same Z1 route.

For every m, `bose_value` and `mixed_value` evaluate the normalized word
to 1. In particular this checks a four-boson term, a two-Fermi term with
no bosons, mixed two-Fermi/one-boson and two-Fermi/five-boson words, and
the vacuum case. These supply genuine nonzero coefficients. The concrete
odd swap evaluates to -1, a repeated odd component to 0, and any Bose
permutation preserves the value. The group in these examples is Unit;
these are statistics/interface controls, not SM or Weyl-current dictionaries.
Z1 separately covers arbitrary actual field and group actions.

## Z3 — Published Finite Local Coordinates

The complete scalar local example reuses the proved identity contraction,
normalized probe and local completeness. It supplies an original
finite-local/statistical coefficient with no exchange generators and no
extra source relations. Its value on u tensor w is u*w.

`FiniteLocal.old_roundtrip` recovers that original input through the empty
extra-relation equivalence. `coordinate_value` evaluates the quotient of
the computed input map to the same u*w, and `reconstruction` checks the
inverse coefficient map. The original finite-local route therefore remains
usable independently of the represented mixed-source route. This example
does not replace a model's own contraction/completeness/exchange obligations.

## Z4 — Nonderivative Values In An Actual EOM Model

`GUT.NonDerivativeModelChecks.Scalar.freeCoefficient n c` uses the existing
globally Lorentz-invariant functional annihilating the entire free EOM
differential ideal and all IBP. Its value on phi^n is c; extraction through
the common quotient gives the same value. The actual image at derivative
degree zero has dimension one at every n, including n=0.

For the interacting scalar, `interacting_values` checks the exact existing
criterion: a global coefficient taking phi cubed to c exists iff lambda*c=0.
`interacting_one_rejected` supplies the concrete negative test at lambda=1,
c=1. Thus a value permitted by the nonderivative off-shell/free input need
not extend to the full interacting EOM input. This is the effect of the
added equations, with no change to the old interface or hidden grading claim.

## Z5 — Nonderivative Higgs Input Selection

`GUT.NonDerivativeModelChecks.Higgs` proves invariance of rho and its powers
under the actual combined global covering-SM/Lorentz action. It selects
the span of rho squared and rho cubed in `HiggsStandardInput.input a b`.
The selection uses the preimage of the full generated EOM/IBP relations,
retaining relations involving derivative representatives or other field counts.

An admitted global coefficient restricts to this nonderivative source with
unchanged extraction on both powers. `imageEquiv` and `image_agreement`
identify its source with the actual image in the full quotient; coefficient
reconstruction and direct/generated evaluation also agree. No assertion is
made that this image has dimension two, that both values are independent,
or that every selected invariant coefficient extends globally.

## Literature And Conclusion Boundary

Selected nonderivative primary-source terms were reinspected:

- Henning et al., [1507.07240v1](https://arxiv.org/pdf/1507.07240v1),
  Eq. (3.11), and [1706.08520v1](https://arxiv.org/pdf/1706.08520v1),
  Eq. (6.3): the one-species zero-derivative powers and phi^4 term motivate
  the scalar controls. The four-dimensional actual free result is Z4;
  this does not supply the missing two-species or positive-degree bridges.
- Grzadkowski et al., [1008.4884v3](https://arxiv.org/pdf/1008.4884v3),
  Eq. (2.1) and Table 2: rho squared and Q_phi=rho cubed are exactly the
  nonderivative representatives in Z5, with the already proved Higgs
  field/dual dictionary. Selection/evaluation does not prove a Warsaw count.
- Li et al., [2005.00008v3](https://arxiv.org/pdf/2005.00008v3),
  Eqs. (4.20)–(4.21): the two-odd/five-even pattern motivates a Z2 input
  instance. Only its statistics are tested here; no full Lorentz/gauge,
  species or flavor identification with those SM operators is asserted.

All checks pass in these scopes. Both the original nonderivative and new
zero-degree routes can be used with the supplied coefficients, while the
EOM route imposes its stated additional relations. The
[six-case derivative comparison](literature-recheck.md) keeps its earlier
partial basis and physical-dictionary boundaries. No paper-wide validation,
generated interaction, analytic action or quantum equivalence is inferred.
