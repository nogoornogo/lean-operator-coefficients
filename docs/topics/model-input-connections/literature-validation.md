# Source Comparisons And Artificial Models

The three pinned primary sources were reopened. The comparisons keep the
predecessors' component, charge and complexified-conjugate conventions.
Sources guide the formulas; no external theorem premise is imported.

| Source and inspected location | Connection checked | Scope and outcome |
| --- | --- | --- |
| Angelescu–Bally–Blasi–Goertz, [2104.07366v2](https://arxiv.org/html/2104.07366v2), Sec. II.2 (5)–(10), Appendix C (24)–(25) | `SU6BoundaryFieldConnection.dictionary`, `upDictionary`, `downLeptonDictionary` and the separate `sterileDictionary` give exact joint gauge/circle field identifications; `joinFromVacuum_agrees` recovers the scalar-dressed wedge and `boundary_pairing` its invariant contraction | Agreement for the already constructed unmixed amplitudes and internal tensors. Source (9)–(10) mix modes: those analytic light profiles and a complete brane action are not identified with the unmixed spaces. This narrower comparison continues independently of that boundary. |
| Dreiner–Haber–Martin, [0812.1594v6](https://arxiv.org/pdf/0812.1594v6), (3.1.1),(3.2.1),(4.3.2)–(4.3.8) | `LagrangianFieldInputConnection.paperCoefficientEquiv` composes the independently proved paper-density dictionary with an actual field-coordinate change; `paper_evaluation`, `full_relations` and `roundtrip` preserve complete coefficient values and generated EOM/IBP relations | Agreement for one scalar/Weyl model with the retained component normalization and independent formal conjugate labels. The source's broader flavor matrices, physical conjugation/reality and mass diagonalization are not new outputs. |
| Sardanashvily, [1206.2508v1](https://arxiv.org/pdf/1206.2508v1), Sec. 6 (31), Theorem 16/(37) | Existing `GradedEulerComparison` checks remain the Euler/first-variation basis; new `independent_density_covariance` and cancellation connection reuse the actual semantic Euler route and full summed density | Agreement in the local-polynomial evolutionary/even-variation specialization. The geometric/cohomology theorem remains outside the comparison. |

The PDF text was inspected for the two PDF sources; the versioned HTML was
inspected for the SU(6) source. No source disagreement required changing a
formula. The limited analytic scope of the SU(6) comparison did not stop the
other sources or the artificial controls.

## Complete Validation Matrix

| Planned case/control | Evidence and interpretation |
| --- | --- |
| SU(6) boundary amplitudes | Constructed component maps, both inverse laws, joint gauge/residual actions, separate Weyl/dual choices and neutral sterile amplitude in `FieldConnection` |
| Lepton-parity mass radical | Constructed inclusion/extraction, `dictionary_agrees`, species/Weyl evaluation, mixed roundtrip and `physical_controls` |
| Complete local density | Odd sign-change generator theorem, `full_relations`, `selected_relations`, `selectedImageEquiv`, evaluation and roundtrip |
| Nonabelian retained action | `S3FieldConnection.dictionary`, `coefficient_nonzero`, `exchange_preserved` and retained `flavor_boundary` |
| Proper target inclusion | `FieldSelectionControls.left_inverse` and `missing_component`: the left inverse does not reconstruct the whole selected space |
| Wrong conjugate/action map | `wrong_map_rejected`; the predecessor's explicit `wrong_conjugation_not_invariant` remains a source convention regression |
| Extra light pair | `Physics.FieldSelectionControls.unchanged_index`, `extra_pair_light`, `no_exact_dictionary`: the dual index agrees but no equivalence to the smaller target exists |
| Noncommuting selectors | `selectors_idempotent`, `selectors_not_commuting`, `common_zero`, `product_range_not_common` |
| Broken interaction symmetry | `Physics.FieldSelectionControls.broken_density`, using the independently nonzero Lorentz-transforming Grassmann probe |
| Fixed/nonfixed vacuum | `fixedInsertion_nonzero`, `nonfixed_vacuum`; concrete SU(6) `joinFromVacuum_agrees` uses its proved fixed brane vector |
| Mixing lifts a light space | `mixing_lifts`, through the actual invariant paired mass |
| Neutral nonzero control | `neutral_nonzero`, the nonzero S3 coefficient, the predecessor's bounded neutral B1 control and the constructed Yukawa witnesses |
| Full-relation selection | Exact comaps, `imageEquiv_projection`, `selectedCoefficient_evaluation`, concrete selected-image equivalence; global extension is still refuted by `extension_still_required` |
| Total-density cancellation | `cancelling_relations` and `cancelling_connection` keep only the full IBP range; the existing no-equation-union counterexample is retained |

The generic proofs use linear inverses and functoriality rather than finite
coordinate tables. Small arithmetic witnesses occur only in explicit negative
controls and do not supply a completeness premise.

Builds, audits and fresh-source measurements belong to [verification](verification.md).
The central literature list and source-location ledgers link these results
without duplicating this test matrix.
