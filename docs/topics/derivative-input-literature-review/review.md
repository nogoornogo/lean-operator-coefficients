# Using The Necessary-Condition Input On Literature Examples

All six pinned papers have been reinspected at the
[specified locations](references.md). The new API makes support, relations
and coefficient-extension obligations explicit. It does not automatically
turn the preceding partial basis comparisons into complete ones.

## Application Method

Start with a precise source U, actual action and stable relation module T.
Specify whether the request concerns all coefficients or evaluation on a
selected target. The common input uses the quotient Q = U/T.

| Requested test | Evidence needed before using the API |
| --- | --- |
| Charge necessity via `scalar_iff` | Actual scalar action on Q and nontrivial Q; raw field labels alone do not suffice |
| Charge test allowing zero support | `scalar_supported_iff`; a zero Q needs no charge detector |
| Constituent test via `no_shared_iff` | Semisimplicity of the actual quotient representation |
| Transfer after more equations | Stability of the added relations; `forbids_extend` transfers prohibition forward |
| Convert global target vanishing to selected-input prohibition | Actual restriction surjectivity in `target_selected_iff` |
| Admit a proposed evaluation functional | Equivariance and annihilation of every imposed relation |

No selected-source decomposition, support enumeration or invariant extension
is inferred. For a residual-only charge test, local invariance must already
be accounted for in U. A scalar character test does not replace Lorentz
invariance. These are conditions for applying specific tests, not a newly
proved classification of every usable Lagrangian or field input.

## Six-Case Review Outcomes

| Case | Use of the new input conditions | Local outcome and remaining obligation |
| --- | --- | --- |
| C1 / [R1](https://arxiv.org/pdf/1507.07240v1) | Compare actual quadratic IBP input with the input after free EOM; apply zero-support guard and relation monotonicity | Direct worked use. Neutral off-shell coefficient survives; on-shell quotient is zero. The two-species dictionary/count gap remains. |
| C2 / [R2](https://arxiv.org/pdf/1706.08520v1) | Test actual free Lorentz quotient before inferring support or a common trivial constituent | The named two-derivative representative is killed. Four-derivative invariance supplies neither a nonzero quotient coefficient nor a complete invariant span. Source/group dictionary and completeness remain open. |
| C3 / [R3](https://arxiv.org/pdf/1008.4884v3) | Use the full EOM input and its selected restriction to constrain admissible evaluations across field counts | Direct worked component relation. Arbitrary five-value data need not define a coefficient. Physical weak/dagger interpretation and the doublet helper derivation remain open. |
| C4 / [R4](https://arxiv.org/pdf/2005.00059v6) | Check whether the raw three-polynomial probes annihilate actual IBP before treating them as coefficients | Existing countercontrol rejects a raw probe as a quotient functional. No three-coordinate quotient equivalence follows; physical invariant completeness remains open. |
| C5 / [R5](https://arxiv.org/pdf/2005.00008v3), R4 Table 5 | Compare the available mixed input's relations/action with the proposed free physical EOM input | Actual signs and IBP remain useful off-shell certificates. Free Weyl relations and the physical group/current dictionary are absent. New prohibition tests cannot supply them or infer a surviving physical current. |
| C6 / [R6](https://arxiv.org/pdf/1811.09413v2) | Preserve actual coefficient evaluation through the existing helper/direct identification; use the parent scalar necessary condition | Direct worked use on the constructed quartic model. A nonzero cubic evaluation requires zero leading coupling. This is a local consequence, not a claim stated by the paper or an all-order field-redefinition theorem. |

Every local stop advances the review to the next row. All six rows are
terminal for this documentation survey. The existing proof statuses remain
C1–C5 partial and C6 proved for its constructed polynomial contract.

## Example 1 — Neutral Does Not Imply A Surviving Coefficient

R1 Eq. (3.11) gives a one-species series without derivative terms after
free EOM and IBP. The repository independently proves a finite instance:
`DerivativeLiteratureScalar.offInput` has a one-dimensional quadratic IBP
source, while `onInput` has zero source after the free equation.

Use `zero_source_forbids` on `onInput`, or the supported scalar criterion
with neutral z(g)=1. Its nontrivial-source antecedent is false. In contrast,
`DerivativeProhibitionControls.off_allows` supplies an actual nonzero
functional before adding EOM. `extended_forbids` and
`reverse_monotonicity_fails` make the direction of relation transfer explicit.

This example prevents a mistaken inference from forbidden coefficients to
nontrivial charges. It does not certify R1's general multi-species series.
The actual statements and source definitions are in the
[scalar control](../../../Math/RepresentationTheory/DerivativeLiteratureScalar.lean)
and [necessary-condition control](../../../Math/RepresentationTheory/DerivativeProhibitionControls.lean).

## Example 2 — An Exact Necessary Constraint On Input Values

For the existing component Higgs input let rho be the formal conjugate-pair
quadratic, R = rho times kinetic, and B = rho times box rho. Its explicit
seeds are box H + a H + b rho H. For every admitted global coefficient f,
the proved `DerivativeLiteratureHiggs.normalized_relation` gives

\[
f(R)=\tfrac12 f(B)+a f(\rho^2)+b f(\rho^3).
\]

The proposed values f(R)=1 and f(B)=f(rho squared)=f(rho cubed)=0 therefore
cannot come from that global input, for any a,b. This rejection is a direct
algebraic deduction from the existing theorem, not a new Lean declaration.
Satisfying this single constraint is not proved sufficient to extend an
arbitrary proposed tuple to a global coefficient.

Use the complete relation preimage when selecting the five representatives.
`selected_extraction` preserves evaluations of already admitted global
coefficients; it does not assert that arbitrary selected values extend.
The parent's `target_selected_iff` requires actual restriction surjectivity
for its converse. Its generic unipotent counterexample shows why this
premise cannot be silently dropped; it does not prove nonsurjectivity for
this particular Higgs input.

R3 Eq. (5.3) motivates the reduction and retains other operator classes.
The displayed exact a,b coefficients belong to this project's chosen
gaugeless, Yukawa-free component normalization. They are not a literal
full-SM rewriting of the paper. The
[source](../../../Math/RepresentationTheory/DerivativeLiteratureHiggs.lean)
still has independent formal conjugate labels and trivial residual action.

## Example 3 — A Necessary Coupling Condition In The Helper Model

The constructed C6 model has

\[
L_0=\tfrac12(\partial\phi)^2-\tfrac g4\phi^4,
\qquad E=\Box\phi+g\phi^3.
\]

The existing helper/direct ideal equality and inverse coefficient maps
preserve evaluation. The parent's actual Lorentz theorem
`ScalarProhibitionConditions.cubic_constraint` therefore applies after
conversion to the direct input: every admitted f has g times f(phi cubed)=0,
since box phi is already an IBP divergence. A proposed global cubic
evaluation of one is incompatible with nonzero g. Zero g is necessary
for such an evaluation; existence at zero g is not asserted here.

For example this checks a request about the cubic operator, rather than
claiming that all scalar coefficients vanish or that a Wilson coupling is
computed from symmetry. The new restriction is our use of the existing
constructed model. R6 Eq. (3.2) instead motivates distinguishing the
first-order EOM response from retained higher terms. Neither that paper
discussion nor a raw second-order nonzero polynomial establishes nonzero
quotient support or quantum equivalence in this project.

See the [helper/direct identification](../../../Physics/FieldTheory/Jets/DerivativeLiteratureScalar.lean)
and [actual scalar parameter theorem](../../../Physics/FieldTheory/Jets/ScalarProhibitionConditions.lean).

## Practical Result And Boundary

The new conditions give concrete rejection tests for proposed inputs and
make the proof route explicit. The clearest present examples are C1's
support change, C3's cross-count evaluation law and C6's coupling restriction.
C2, C4 and C5 identify missing prerequisites rather than establish additional
basis counts. In particular, `probe_not_ibp` in C4 is an actual failure of
input admission, not a contradiction of Murphy's basis.

A useful next proof, if separately requested, would be a bounded actual
invariant quotient and inverse coefficient presentation for one selected
sector. The new tests locate that obligation; they do not eliminate it.
No deferred foundation has been reopened by this review.
