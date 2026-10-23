# Comparison Results

All six entries reached a local terminal outcome, in the planned order.
C1–C5 retain narrower checked results and explicit prerequisite gaps; C6
passes its finite polynomial contract. This is not six complete basis
validations. No paper theorem or count is a proof premise.

## C1 — Partial

[Math scalar source](../../../Math/RepresentationTheory/DerivativeLiteratureScalar.lean):
`off_dimension` proves dimension 1 of the actual one-species, two-field,
two-derivative IBP quotient. `second_eom` places the second-jet monomial in
the actual free-equation projection kernel; `on_relations_top`,
`on_dimension` and `on_coefficient_zero` prove that adding EOM makes the
quotient and every coefficient zero. Both use common input operations;
the on-shell source is the existing untruncated linear-EOM construction.

The [independent exact diagnostic](../../../tools/derivative-literature/check-one-dimensional.py)
enumerates full finite monomial sectors and actual Leibniz/EOM rows. It
reproduces (1,1,0) and (1,1,1) for two-species multiplicities (1,1)/(2,2)
at derivative degrees 0/1/2. Those six multi-content counts are **not**
Lean-certified: their coordinate presentation has no proved transport to
the selected actual jet subspace and its full relation preimage. The
degree-zero comparison for those contents is likewise not newly certified.
This is the local multidegree bridge stop, followed by C2.

## C2 — Partial

[Physics scalar source](../../../Physics/FieldTheory/Jets/DerivativeLiteratureScalar.lean):
`two_projection_zero` and `two_coefficient_zero` prove that the representative
phi squared times the scalar kinetic contraction vanishes in the actual
Lorentz free-EOM/IBP input. `four_invariant` proves invariance of the
four-first-derivative candidate; `four_extraction` tests its common input
evaluation. These statements concern the actual Lorentz action in signature
(+---), not a finite subgroup or a supplied invariant-span premise.

The [finite diagnostic](../../../tools/derivative-literature/check-scalar-lorentz.py)
uses source dimensions 1/20/305 at derivative degrees 0/2/4. EOM/IBP row
ranks are 0/11/235; adding six infinitesimal Lorentz constraint families
gives ranks 0/20/304, hence diagnostic coefficient dimensions (1,0,1).
The exact computation is supplementary. Its jet-coordinate transport,
infinitesimal/full-group equivalence and Euclidean/complex-Lorentz dictionary
have not been proved in Lean. G1 remains: no complete invariant coefficient
basis, or nonzero class at degree four, is claimed. Then C3 was processed.

## C3 — Partial

[Math Higgs source](../../../Math/RepresentationTheory/DerivativeLiteratureHiggs.lean)
uses four independent commuting component/conjugate labels and four ordinary
derivatives. `literal_reduction` proves an exact polynomial identity;
`reduction_mem` puts it in the full differential EOM ideal plus actual IBP.
`normalized_relation` proves

\[
f(\rho K)=\tfrac12 f(\rho\Box\rho)+a f(\rho^2)+b f(\rho^3).
\]

The formal seeds are Box H + a H + b rho H, and the corresponding conjugate
label seeds with the same parameters. The theorem holds algebraically for
complex a,b; the planned real-coupling specialization follows by casting.
`selected` retains the full relation preimage on the five-representative
span; `selected_extraction` checks restriction of global coefficients. The
implementation retains both potential terms and does not quotient each
field count separately.

This is an algebraic reading of the gaugeless relation, with trivial residual
action. G2 remains for the actual weak/hypercharge/conjugation dictionary.
The doublet leading Lagrangian's helper-generated Euler family has **not**
been identified with these seeds. No two-operator Higgs basis or physical
SMEFT input is certified. These gaps are retained instead of treating the
formal labels as an already proved physical dictionary. Then C4 was processed.

That was the comparison checkpoint. The subsequently authorized
[foundation extension](../derivative-literature-foundations/progress.md)
now proves the Higgs helper Euler/direct-ideal connection and an actual
global SM/Lorentz input with a paired field/dual dictionary. Its own
dossier and verification state the new scope; the earlier trivial-action
certificate is unchanged.

## C4 — Partial

In the same [Math source](../../../Math/RepresentationTheory/DerivativeLiteratureHiggs.lean),
`q1`, `q2`, `q3` are the three ordinary-derivative contractions with the
index pairing of Murphy v6 Table 2 and the explicit (+---) metric.
`probe_values` proves a separating raw-polynomial matrix with rows
(1,1,1), (0,-1,0), (2,2,0); `raw_independent` proves linear independence
in the unquotiented component polynomial algebra.

This does not establish independence after EOM/IBP or spanning of the
invariant quotient. `probe_not_ibp` explicitly evaluates an actual total
derivative to 1, so these raw probes cannot be descended as coefficient
functionals. G1/G2 remain for actual invariant completeness and the physical
doublet dictionary. This check independently ran after C3's stop, and C5
followed it; it does not rely on C3 having passed its complete contract.

## C5 — Partial

[Physics mixed source](../../../Physics/FieldTheory/Jets/DerivativeLiteratureMixed.lean)
transcribes a two-component Pauli current, the bidirectional Higgs derivative
current, rho and the factor of i into the actual exterior/polynomial algebra.
`odd_swap` and `current_reorder` prove the Grassmann reorder sign.
`current_ibp` moves a derivative using the actual even total derivative,
with the differentiated fermion/Higgs factors retained. `candidate_extraction`
checks common input evaluation.

These are off-shell algebraic and IBP statements with trivial residual action.
Free Weyl EOM are **not** imposed on this test input. No physical Lorentz/
weak-equivariance or Li/Murphy four-component current equivalence is claimed.
Existing paired Weyl equations and adjoints do not themselves supply the
mixed contraction dictionary. The inspected fixed four-component charge
adapter uses a Euclidean Clifford convention; it cannot simply be substituted
for the required Minkowski/current convention. G1/G2/G4 therefore remain,
including any derivative-index/sign normalization in that physical dictionary.
One-coordinate completeness and Hermitian counting are unproved. C6 ran
independently of these gaps.

## C6 — Proved Finite Polynomial Contract

The [Physics scalar source](../../../Physics/FieldTheory/Jets/DerivativeLiteratureScalar.lean)
constructs the optional helper expression for the specified quartic leading
Lagrangian. `quartic_eval` and `quartic_euler` compute its actual density and
Euler expression. `quartic_ideal` and `quartic_relations` identify its complete
differential ideal and IBP relation with the direct scalar input.
`toDirect`/`toHelper` have both inverse laws and `extraction_agrees` preserves
evaluation for the actual Lorentz action, without a new stability premise.

For actual jet-compatible substitution phi -> phi + epsilon phi cubed,
`substitution_zero`, `substitution_first` and `substitution_second` give the
zeroth, explicit Euler/current first, and retained second coefficients. The
second coefficient is

\[
\tfrac92\phi^4(\partial\phi)^2-\tfrac{3g}{2}\phi^8.
\]

`helper_first_onShell` proves first-order vanishing in the helper input.
`second_raw_nonzero` detects a nonzero raw second coefficient at g=0 by exact
evaluation. This is a constructed local polynomial specialization of R6
Eq. (3.2), not its analytic functional/S-matrix theorem or a verbatim worked
example. Raw nonzero is not nonzero modulo EOM/IBP and does not refute
field-redefinition equivalence.

## Portfolio Boundary

See the [route review](route-review.md), [verification](verification.md) and
[coverage ledger](../../verification/derivative-interface-coverage.md).
No paper mismatch was established. There is no evidence here of a defect
in the common quotient operations; their use does not remove the separate
physical-dictionary and complete-invariant-span obligations. Further work
would address those explicitly identified bridges, not repeat the same
partial results as complete paper validations.
