# Literature And Artificial Validation

Each source was reopened and checked independently. Sources fix conventions
and candidate formulas; none is a Lean theorem premise. Consumers are in
[LagrangianModelLiterature.lean](../../../Physics/FieldTheory/Jets/LagrangianModelLiterature.lean).

| Named comparison | Source and inspected location | Verified result | Boundary |
| --- | --- | --- | --- |
| Two-component Yukawa density | Dreiner–Haber–Martin, [0812.1594v6](https://arxiv.org/pdf/0812.1594v6), (2.21)–(2.22),(2.29),(2.38)–(2.39),(3.1.1),(3.2.1),(4.3.2) | Component/kinetic dictionaries, total-density and Euler-family equality, full relation transport and Lorentz invariance | One neutral Weyl species and one scalar, complexified conjugate components. Scalar kinetic/mass addition is constructed locally. |
| Gaugeless Higgs | Grzadkowski et al., [1008.4884v3](https://arxiv.org/pdf/1008.4884v3), (2.1),(5.3) | Signed redundant-operator identity through the registered coordinate decoder | Gauge/Yukawa couplings vanish; no interacting Warsaw count. |
| First variation | Criado–Pérez-Victoria, [1811.09413v2](https://arxiv.org/pdf/1811.09413v2), Section 3, (3.2) | Constructed quartic first-order term vanishes; second-order raw term remains nonzero | Local polynomial specialization, not an analytic or all-order field-redefinition equivalence. |

## Two-Component Dictionary

The component dictionary chi=(psi_1,-psi_0) gives undotted/dotted contractions
-2 times the left pair and +2 times the conjugate pair. The displayed bar-sigma
kinetic expansion equals the paired kinetic polynomial. Mass/Yukawa parameters
are (-m,conj(m)) and (-y,conj(y)); the kinetic multiplier is i.

These are proved in `undotted_dictionary`, `dotted_dictionary`,
`kinetic_dictionary` and `density_dictionary`. `full_lorentz` consumes
independent density invariance; `coefficient_equations` checks decoded values
against computed EOM. `euler_dictionary` and `full_relation_dictionary` also identify the directly compiled paper syntax; `paperCoefficientEquiv` preserves coefficient evaluation. No sign or normalization is an imported premise.
There is no imposed reality quotient, quantization or amplitude comparison.

The earlier [Tong comparison](../interacting-lagrangian-classification/literature-validation.md)
remains interaction-only. This two-component result does not upgrade it into
a full Dirac dictionary.

## Artificial Models And Negative Controls

| Check | Result and evidence |
| --- | --- |
| Full and selected roundtrips | `LagrangianModelControls` proves inverse maps and target criteria for the mixed cubic. Selection retains the complete preimage without global extension. |
| Cancelling terms | For every p, the model from p-p has zero Euler family and exactly the IBP range. The retained nonlinear counterexample rejects unioning separate equation ideals. |
| Free recovery | `YukawaModelControls.free_odd_recovery` and `.free_scalar_recovery` recover the free equations. Unused even labels have zero EOM. |
| Interacting target relation | Every decoded Yukawa coefficient obeys the scalar wave/mass/fermion-pair equation with both Yukawa parameters. |
| Exact coupling branch | Registered quartic cubic value one exists at g=0 and is impossible at g=1, using the necessary and sufficient g*c=0 criterion. |
| Broken scalar contraction | A same-component left/conjugate product transforms by four under an explicit SL(2,C) boost. A Grassmann probe equals one, proving its noninvariance. |

All three source comparisons pass under these dictionaries. The general
semantic density-to-Euler covariance theorem was left outside this predecessor
checkpoint, not identified as a source mismatch. The
[successor comparison](../euler-naturality/literature-validation.md) now derives
the same model through the general linear naturality theorem. Commands and audits belong to
[verification](verification.md).
