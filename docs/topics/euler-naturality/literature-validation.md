# Literature And Artificial Validation

Both primary sources were reopened independently. Their formulas guide the
comparison and supply conventions; neither is a Lean theorem premise.
A discrepancy would be recorded while the next comparison proceeds. Both
selected comparisons agree in their stated scope.

| Named comparison | Pinned source and inspected location | Proved comparison | Scope |
| --- | --- | --- | --- |
| Graded Euler and first variation | Sardanashvily, [1206.2508v1](https://arxiv.org/pdf/1206.2508v1), Section 6, (31), Theorem 16/(37) | `GradedEulerComparison.multiindex_formula`, `actual_partial`, `first_variation`: actual left partials and word-independent adjoints give the algebraic Euler/variation formulas | Local polynomial evolutionary, even variations. Manifold/cohomology and general contact transformations are outside this comparison. |
| Scalar/Weyl Yukawa density | Dreiner–Haber–Martin, [0812.1594v6](https://arxiv.org/pdf/0812.1594v6), (3.1.1),(3.2.1),(4.3.2), with the retained component dictionary | `EulerDensityConnection.paper_euler` obtains paper-syntax Euler equality from density equality. `automatic_euler` obtains covariance from independent density invariance; `model_eq` identifies the complete existing input | One neutral Weyl species and one scalar, complexified conjugate components, scalar kinetic/mass addition constructed locally. No new flavor, reality or amplitude claim. |

The graded source indexes commuting derivatives once per symmetric multiindex.
The implementation groups word coefficients by that multiindex before applying
the adjoint. Odd partials are actual left Clifford contractions. First variation
keeps the variation on the left and includes an explicit IBP current. No
variational-bicomplex exactness or full geometric theorem is imported.

The Yukawa comparison retains the
[previous sign/component dictionary](../lagrangian-model-connections/literature-validation.md).
The new paper Euler proof uses only density equality and semantic descent;
the previous explicit Euler calculation gives independent agreement. The
automatic and independently certified models are equal, including the complete
generated relation input.

## Artificial Models

| Check | Result |
| --- | --- |
| Semantic zero and cancellation | `semantic_zero`, `cancelling` give zero Euler families from actual density equality. |
| Commuting words in a nonlinear density | `commuting_words_context` permits any word permutation inside a product-plus-summand context. |
| Odd reordering | `odd_reordering` checks the minus sign for arbitrary odd components and derivative words. |
| Arbitrarily high quadratic jet | `high_jet_square` gives twice the adjoint applied to that jet, without an order cutoff. |
| Simultaneous field/direction shear | `shear` is a group representation; `simultaneous_change` checks Euler transport for every mixed density. `direction_mixes` proves a non-diagonal image. |
| Identity recovery | `zero_change` recovers the Euler family for every density. |
| Broken symmetry | `broken_density_rejected` uses the retained nonzero Grassmann probe and explicit Lorentz boost to reject the non-scalar contraction. |

These are Lean proofs over the actual algebra, not sampled computations.
The [verification record](verification.md) owns build and audit results.
