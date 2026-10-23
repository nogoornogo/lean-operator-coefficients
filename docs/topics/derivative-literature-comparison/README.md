# Derivative Interface Literature Comparisons

- ID: `derivative-literature-comparison`
- Status: completed
- Result type: bounded proved comparisons and settled partial-comparison stops
- Working branch: `proof/derivative-literature-comparison`
- Integration target: `master`; explicitly authorized and integrated
- Integration evidence: preserved-history merge and [merged-state verification](master-integration.md)
- Authorization: user-directed topic, fixed-queue execution and subsequent integration of the present results

## Endpoint

Test the derivative interfaces against six fixed literature cases, covering
IBP, linear EOM, nonlinear EOM selection, mixed Bose/Fermi signs and optional
Lagrangian-generated input. Preserve the published nonderivative interface
and all dependency pins. This is a comparison of specified algebraic sectors,
not verification of complete papers or all SMEFT operators.

All six cases reached their recorded local stops. C1–C5 are partial
comparisons; C6 passes the finite polynomial contract. The preceding [helper topic](../local-lagrangian-helper/README.md)
is merged and separately [verified on master](../local-lagrangian-helper/master-integration.md).

## Reading Order

- [Pinned sources and inspected locations](references.md).
- [Execution rules, acceptance gates and stopping policy](plan.md).
- [Six finite case contracts](cases.md).
- [Queue and dependency gaps](queue.md).
- [Results and remaining boundaries](results.md).
- [Bounded route review](route-review.md).
- [Execution audits/builds and planning checkpoint](verification.md).
- [Verified master integration](master-integration.md).

## Portfolio

| Order | Source | Main interface question |
| --- | --- | --- |
| C1 | Henning–Lu–Melia–Murayama, one-dimensional scalars | Does the actual EOM/IBP quotient reproduce small fixed-multiplicity coefficients? |
| C2 | Henning–Lu–Melia–Murayama, four-dimensional scalars | Do actual Lorentz coefficient spaces reproduce the low-derivative four-field sector? |
| C3 | Grzadkowski–Iskrzyński–Misiak–Rosiek | Does full-source nonlinear EOM selection retain the Higgs relation across field counts? |
| C4 | Murphy | Can the three displayed Higgs four-derivative candidates be connected to an actual coefficient basis? |
| C5 | Li–Ren–Shu–Xiao–Yu–Zheng | Does a nontrivial mixed Weyl/Higgs derivative current have the published signs and relations? |
| C6 | Criado–Pérez-Victoria | Does actual polynomial substitution agree with generated first variation without dropping the next order? |

Gaugeless/free specializations are explicit in the contracts. In particular,
the Higgs and mixed cases do not certify the full gauge-covariant SMEFT basis.
The paper results supply comparison targets, never completeness premises.

## Completion And Next Action

The [results](results.md) and [queue](queue.md) give terminal outcomes for
**all six** cases. Each local stop advanced to the next paper. No paper
mismatch or resource stop was established. Remaining multi-content,
physical-dictionary and invariant-completeness bridges are explicit in the
[route review](route-review.md); they were not replaced by theorem premises.

Strict transitive audits, the full build and documentation gates pass.
The shared [bibliography](../../proof/RELATED_LITERATURE.md),
[coverage ledger](../../verification/derivative-interface-coverage.md) and
[proof dossier](../../proof/current/applications/Physics/DERIVATIVE_LITERATURE_CONTROLS.md)
record the actual limited claims. The execution endpoint is settled and
integrated into master. The user will reconsider the remaining theory work
separately; no further case, flavor range or foundational project is started.
The local topic branch is retired after reachability and worktree checks;
its historical name is retained above. No remote update is made.
