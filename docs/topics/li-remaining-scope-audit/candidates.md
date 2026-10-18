# Candidate Classification

| Candidate | Classification | Decision and evidence |
|---|---|---|
| (4.38), six-coordinate conversion | Small helper | Recommend: explicit complex linear inverse, then basis transfer conditional on supplied operator coordinates |
| (4.41), nine-by-four printed matrix | Small helper | Recommend: first four red rows form a basis and full row span has dimension four; EOM explanation is not proved |
| (4.44), twenty-four-by-four printed matrix | Existing API plus small helper | Recommend: first four red rows form a permuted coordinate basis; full row span has dimension four |
| Section 4.3 general coordinate conversion/redundancy | Existing API | Mathlib `Basis.map`, `Basis.span_eq`, matrix row-span rank; apply to the three concrete certificates, not a new general construction |
| D.10/D.13 charged-lepton dipoles | Unresolved literal-source dictionary | Existing `DipoleCoefficientCompleteness.equivB/equivW`, `DipoleGaugeTensor.weakDualEquiv`, `DipoleSpinorTensor.contraction_tmul` classify algebraic sectors, but do not by themselves identify literal angle brackets/Pauli normalization; defer that attribution |
| D.11–D.17 quark dipoles | New interface | Color/adjoint dictionaries and typed charged species need additional consumers; not automatically covered by lepton dipoles |
| General p/y/m-basis | New foundation | Existing statistics/isotypic dictionaries do not prove all Li tableau identifications |
| General j-basis and Section 2 | New foundation | Derivative, on-shell, EOM/IBP and Casimir interfaces absent from the agreed scope |
| ABC4EFT correctness/runtime | Unresolved / excluded environment expansion | No Mathematica execution or software verification |
| Phenomenological matching/rates | Excluded | Outside exact algebraic endpoint |

For all three selected certificates the independent target is `Fin n → ℂ`,
not a differential-operator quotient. Matrix entries are transcribed data;
claims about their actual operator derivation remain explicit boundaries.
