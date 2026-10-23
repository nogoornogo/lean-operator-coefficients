# Literature And Artificial Validation

The [persistent consumers](../../../Physics/FieldTheory/Jets/InteractingLagrangianLiterature.lean)
test the new all-order coordinate transport against independent existing
source dictionaries. Each comparison is limited to its stated target.
All three named source cases were processed; none stopped the remaining cases.

| Source and inspected location | Checked result | Exact scope |
| --- | --- | --- |
| Grzadkowski et al., 1008.4884v3, Eqs. (2.1),(5.3), PDF pp. 3,9 | `Higgs.paper_relation` retains the signed potential/derivative relation after all-order coordinate reconstruction; `complete_roundtrip` preserves every admitted coefficient. | Actual global SM-cover/Lorentz action; real mass/quartic parameters mapped to a=-m²,b=lambda; gauge and Yukawa couplings zero. No Warsaw-basis count. |
| Criado–Pérez-Victoria, 1811.09413v2, §3 Eq. (3.2), PDF p. 10 | `Scalar.first_order_on_shell` vanishes for every all-order coordinate family; `higher_order_not_erased` retains a nonzero quadratic substitution term; `cubic_value_iff` is exactly g*c=0. | Constructed quartic scalar specialization, actual Lorentz action and full generated EOM/IBP. The paper's first-order/higher-order distinction is preserved; no quantum or all-order field-redefinition equivalence. |
| David Tong, QFT HTML §5.6, Eq. (5.475) | `TongYukawa.density_eval` is the literal interaction -g phi sum_a(barPsi_a Psi_a), with four component pairs. All nine Euler components have checked left-Grassmann signs, and `complete_roundtrip` validates their all-order generated-input coordinates. | The interaction part only. Barred/unbarred components are independent complex odd labels. The consumer uses a trivial group; the full Dirac kinetic term, Lorentz dictionary, scattering and rates are not certified. |

Primary locations were reopened and the two PDF formulas inspected. Equation
(5.3) is a schematic operator-class relation; the numerical scalar coefficients
come from the separately proved gaugeless density. Tong's HTML equation number
is used here, rather than assuming PDF numbering agrees.

## Artificial Results

[PolynomialPotentialClassification](../../../Math/RepresentationTheory/PolynomialPotentialClassification.lean)
proves an entire nonlinear family, at all powers n and all coefficient orders:
potential lambda*X^(n+1)/(n+1), equation lambda*X^n, admitted values exactly
lambda*c_(n+k)=0. Nonzero coupling has n independent coordinates, while zero
coupling has an unrestricted sequence. Prescribed-value existence is proved
in both directions, including n=0 and parameter degeneracies.

[InteractingLagrangianControls](../../../Math/RepresentationTheory/InteractingLagrangianControls.lean)
checks the mixed cubic Euler constraints, both odd signs and exact zero-coupling
recovery of the full IBP source. Opposite potentials cancel before variation;
the union of their separate equation ideals is proved different. The cutoff
counterexamples distinguish an all-order presentation from finite observations.

These are proof-level controls on complete relations. They use no finite
truncation, numerical rank estimate or external counting premise. The generic
selected-source theorem retains the full relation preimage without a global
invariant-extension hypothesis.

## Outcome And Remaining Boundary

No disagreement occurs in the inspected scalar/Higgs identities or literal
Yukawa interaction. The comparisons validate exact coefficient transport and
generated equations. They do not certify complete papers or solve the infinite
constraint system for every density. The [dossier](../../proof/current/core/Math/INTERACTING_LAGRANGIAN_COORDINATES.md)
separates the general necessary/sufficient presentation from closed-form counts.
