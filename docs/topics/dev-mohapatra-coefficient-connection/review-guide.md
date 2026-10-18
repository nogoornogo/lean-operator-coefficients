# Independent Review Guide: Dev–Mohapatra Coefficient Evaluation

## Request to the reviewer

Please critically review the conditional coefficient evaluation below.
Separate mathematical correctness, correspondence to the supplied action,
and correspondence to the paper. Do not treat a successful Lean build as
proof that the supplied UV action recovers suppressed source conventions.
Report concrete counterexamples, missing hypotheses, normalization mistakes
and overstatements, with file/declaration or paper equation references.

The purpose is to determine how strong the discrepancy is and exactly what
source information would be needed to resolve it. This is not a request to
confirm a paper error or to estimate phenomenological consequences.

## Result being reviewed

Target: Dev–Mohapatra, arXiv:1504.07196v2, especially Eqs.(1), (3), (4) and
Fig.1. Eq.(4) displays a six-quark inverse-C operator with scalar
`(lambda*z)^2 / (16*pi^2*Mchi^4*MN)` and H.c.

For a supplied canonical, derivative-free one-N action and the selected u,d,s
channel, exact scalar and all-degree heavy Grassmann elimination yields the
coefficient of the adopted lower-block inverse-C operator
`-(lambda*b)^2 / (2*Mchi^4*MN)`.

With b=z the ratio to the printed scalar is -8*pi^2. With the ordered
antisymmetric flavor sum without a half, b=2z and the ratio is -32*pi^2.
A flavor half returns the first interpretation. An overall action sign is
not by itself a certified sign error in the paper.

The actual eighteen-component operator is proved nonzero. Under nonzero
masses and selected couplings, the projected actions with these coefficients
are proved unequal. The statement concerns the unbarred selected channel;
it does not assert that the full effective action contains no other terms.

## Recommended reading order

1. [Current evaluation](literature-evaluation-results.md).
2. [Nonzero-action and normalization result](normalization-closure-results.md).
3. [All-degree elimination result](heavy-elimination-results.md).
4. [Hermitian-action result](hermitian-results.md) and [tree action dictionary](tree-level-results.md).
5. [Literature convention survey](related-conventions-results.md), [fixed inspection](convention-results.md), and [source register](references.md).
6. [Verification ledger](verification.md), then the Lean sources listed below.

Earlier phase records retain earlier boundaries; the later all-degree and
closure records supersede the missing-heavy-elimination boundary. Historical
phase completion must not be read as independent source matching.

## Proof map

| Claim | Source / principal declarations |
| --- | --- |
| Initial action, Majorana half, six-quark coefficient and determinant witness | `DevMohapatraTreeLevel`: `generated_printed`, `uv_sequential_on_shell`, `probe_printed_evaluation`, `generated_nonzero` |
| Explicit related-source C matrices, right/lower block and operator transport | `DevMohapatraLiteratureConvention`: `generated_literature`, `paper_comparison`, `ordered_paper_comparison` |
| Literal H.c. action and scalar elimination | `DevMohapatraHermitian`; supplied action and source definitions |
| Finite exact heavy inverse and odd solution | `DevMohapatraHeavyElimination`: `kernel_nilpotent`, `source_unique`, `solution_odd` |
| Actual left action derivatives and stationary substitution | `DevMohapatraHeavyAction`: `differentiated_action`, `stationary_unique`, `eliminated_action` |
| Projection to selected holomorphic channel | `DevMohapatraHeavyProjection`: `project_eliminated_action` |
| Full H.c./scalar-action transport | `DevMohapatraHeavyHermitian`: `action_dictionary`, `holomorphic_full_action` |
| Stationary substitution respects H.c. | `DevMohapatraHeavyConjugacy`: `solution_adjoint`, `evaluate_hc`, `eliminated_hermitian` |
| Direct all-degree comparison | `DevMohapatraCoefficientReevaluation`: `independent_comparison`, `ordered_comparison` |
| Actual inequality and matching conditions | `DevMohapatraNormalizationClosure`: `operator_nonzero`, `action_ne_paper`, `ordered_action_ne_paper`, `normalization_match_iff`, `consistent_bilinear_match_iff` |

Sources live in `Physics/StandardModel/Operators/`; corresponding persistent
strict audits live in its `Audit/` directory. Shared mathematical modules and
the optional bundle builder can collect repository-local import dependencies.
The source, rather than this navigation table, determines exact theorem types.

## Questions requiring particular scrutiny

- Are mass and vertex signs transported consistently with inverse C, chirality
  and the order reversal in physical Hermitian conjugation?
- Do the scalar source terms and their H.c. reconstruct the intended supplied
  action, and does left Grassmann differentiation give its stated residual?
- Does finite kernel nilpotence justify the complete inverse, without silently
  omitting higher-degree terms or assuming barred-heavy components vanish?
- Is the extraction of the unbarred channel the appropriate comparison to
  Eq.(4), including the antisymmetric flavor sum and operator normalization?
- Does the nonzero witness map to precisely the carrier used in the action
  comparison, rather than to a different tensor or quotient?
- Which conventions in the related papers are actually adopted by the target?
  A reference alone is not proof of adoption.
- Could a source-supported coupling, kinetic, operator or mass normalization
  satisfy the matching condition below? Distinguish supported evidence from
  an arbitrary compensating choice.
- Are any remaining documentary ambiguities incorrectly presented as proved
  algebraic facts, or any proved algebraic steps still called missing?

## Matching condition and its interpretation

Write component parameters as mu*m, nu*M, a*lambda, b*z, and the comparison
operator as t*O. For nonzero original masses/couplings and nonzero mu,nu,
matching the action polynomials is equivalent to

```
-8*pi^2*(a*b)^2 = t*mu^2*nu.
```

This is a family of independent parameter identifications. It is not a
classification of arbitrary field redefinitions, nor does it certify kinetic
normalization. Nonzero a,b,t are additionally required for invertible
identifications. A consistent common bilinear change scales the mass and
vertices by c and the three-bilinear target by c^3; it preserves whether the
coefficients match. Do not confuse that change with rescaling only O.

## Verification and explicit boundaries

Baseline before this review package: commit `checkpoint 01` on the historical
`proof/dev-mohapatra-coefficient-connection` branch. Full `lake build` passed
6739 jobs. Nine closure declarations passed strict transitive axiom audits;
only propext, Classical.choice and Quot.sound are permitted. Earlier all-degree
proofs and their audits are recorded in the verification ledger. No sorry,
custom axiom or new audit exception was admitted for these results.

The scripts are independent bounded computational checks, not Lean premises.
They do not replace the all-degree proof. The last phase changed no action or
convention definitions and therefore did not rerun those prior scripts.

Unproved application inputs include source adoption of the spinor/kinetic
conventions, canonical scalar normalization, printed-to-component coupling
identification, exact flavor sum, and signed Lagrangian/Hamiltonian convention.
Original Hermitian scalar UV transport requires a real nonzero scalar
quadratic parameter. No loops, derivative expansion, physical amplitudes,
rates, QCD, additional N or flavors, or paper-error certification is claimed.

## Subsequent review closure

The [magnitude obstruction](review-closure-results.md) now proves arbitrary
unit-phase exclusion and an explicit bounded compensation obstruction, with
actual action inequality. It does not prove universal rational/algebraic
normalization exclusion. This addition does not change the source-adoption
boundary or independently validate the external review's rate estimates.

## Suggested review output

Provide (1) a verdict for each proof/source bridge, (2) issues ranked by
severity with precise evidence, (3) any alternative source-supported dictionary
and its implied matching multipliers, and (4) the narrowest defensible claim.
State when an issue needs new source information rather than more algebra.

## Archive contents and use

The previously generated ZIP was deleted at the user's request. Review the
linked documents and sources directly. If a future archive is requested,
run `python3 tools/dev-mohapatra/build-review-bundle.py` from the repository
root. It creates `/tmp/dev-mohapatra-review.zip`, preserving repository paths,
with topic documents, the reader-facing model study, the current proof dossier,
all Dev–Mohapatra Lean sources/audits and their local import closure, bounded
check scripts, pin/build metadata and a SHA-256 manifest. Third-party PDFs,
mathlib/TauCeti dependencies, build outputs and credentials are excluded.
Source URLs and inspection hashes are in references.md. Follow those links
for independent paper inspection. Links to other repository documentation may
point outside this selected archive; it is not a full repository checkout.
For Lean rebuilding, use the original pinned repository/dependencies; the
archive is a review snapshot, not a standalone Lean project.
