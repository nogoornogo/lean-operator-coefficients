# Boundary Construction Verification

The [frozen endpoint](boundary-plan.md) is an algebraic boundary input, with
analytic mixed-mode admission kept separate. The [model result](../../model-studies/su6-protection/boundary-model.md)
states the theorem inputs and application boundary. The earlier mass-radical
obstruction retains its own [verification](verification.md).

## Versioned Source Correspondence

The full text used is [2104.07366v2 HTML](https://arxiv.org/html/2104.07366v2).
The source supplies the model conventions, not a Lean axiom or a branching
completeness premise.

| Source location | Lean comparison | Outcome |
| --- | --- | --- |
| (4), SM-preserving boundary limit | Actual standard (-2,3) SM-cover action, color-first coordinates | Retained SM action intertwines the selected components. The entire boundary gauge stabilizer is not classified. |
| (5), left twenty signs | UV zero, IR complement of the split up-right embedding | Left amplitudes zero; complementary right space exactly Color, with actual 6Y=4 action. |
| (6), left fifteen signs | Projectors on the proved five-block exterior-square equivalence | Exactly left Q and ec, no right amplitudes; no unproved complete branching premise. |
| (7), left six signs | Singlet projection at both ends | Left sterile singlet, right color plus weak; SU(2) epsilon gives the physical lepton dictionary after conjugation. |
| (8), extra singlet | Identity/zero left projectors | Both unmixed selected chiral spaces zero. |
| (9), chi / barred-psi convention | Natural scalar-wedge contraction, dual first field | UV tensor invariant; wrong direct-field sign gives a nontrivial C4 character. |
| (10), IR internal mass mixings | Scalar contraction from cube to square, square to six, six to singlet | Each constructed tensor is baryon-invariant; color/weak restrictions follow from the same square contraction. Full printed brane-action normalization is not matched. |
| Appendix C, (24)–(25) | Actual SU(6) compensator and all-exterior-degree central factorization | Residual charge is 6B in an integral covering parametrization; scalar singlet and weak–singlet Higgs entry fixed. |
| Appendix C, anomalous baryon symmetry | Explicit quantum boundary | No anomaly cancellation or quantum-exact proton-stability theorem. |

The uniform projector and exterior identities replace component enumeration.
`contract_embed` is a left inverse on the cube; the selected-image criteria
prove exhaustiveness of the algebraic selection. `strip_join_pure` and
`stripSquare_vev` establish retractions for the boundary contractions.
Changing which chirality is complemented does not pass these same criteria:
`left20_zero` and `right15_zero` record the discarded chiral spaces explicitly.

## Coefficient Checks And Controls

- The actual left fifteen and right twenty/six gauge maps give Q, ec, uR,
  dR and conjugate L. Their derived baryon phases agree with the C4
  SM/Higgs input; multiplicity spaces carry the same scalar action.
- `bounded_light_forbidden` closes the existing three-generation bounded
  input at q=2,l=0. `all_degree_b1` also covers arbitrary fermion/Higgs
  degrees and arbitrary complex multiplicities on the ten signed SM species.
- `neutral_control` uses an existing actual nonzero coefficient when the
  protecting residual action is removed. This prevents interpreting boundary
  selection or statistics alone as the protection mechanism.
- `wrong_conjugation_not_invariant` rejects the direct-field reading of
  unbarred psi. The central degrees come from `exterior_factor` rather than
  a separate charge table used as a premise.
- `derivative_selected_forbidden` works on the full stable relation input.
  Selected stability and the selected charge action are retained explicitly;
  it does not establish a paper-specific interacting EOM module or assume
  extension of selected coefficients to a global source.

## Lean And Repository Acceptance

Commands use two Lean threads, a 16 GiB virtual-memory cap, disabled core dumps
and a 540-second timeout per command. New files and the audit are registered
in the subject aggregates. No dependency pins, proof limits, prior audits or
axiom allowlists are changed. Compilation of the new sources is distinguished
from replay of dependency artifacts.

The strict audit collects every declaration in the new Math, Physics and GUT
namespaces, including private/generated helpers, and permits only `propext`,
`Classical.choice` and `Quot.sound`. Its required-consumer list includes the
actual cube/gauge maps, projectors, baryon factorization, interaction checks,
negative controls and full-relation selection theorem.

| Command | Result |
| --- | --- |
| `lake build GUT.SU6.Audit.AuditBoundaryProtection` | PASS; all eight new modules compiled across focused runs; final dependency graph 4,471 jobs |
| `lake env lean -j2 GUT/SU6/Audit/AuditBoundaryProtection.lean` | PASS; 295 strict transitive declaration checks, freshly executed rather than replayed |
| `lake build Math` then `lake build Physics` | PASS; aggregate checks serialized, 7,472 and 7,067 jobs |
| `lake build` | PASS; 9,746 jobs, GUT aggregate compiled; dependency results may be cached/replayed |
| `node tools/layout/check-layout.mjs` | PASS; 4,249 modules, layers/imports/cycles/aggregate/relocation checks |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or anchors |
| `python3 tools/docs/check-topic-index.py` | PASS; existing topic and settled outcome retained |
| `python3 tools/docs/check-work-metadata.py` | PASS; no work dates, local paths or local commit IDs introduced |
| `node tools/docs/render-structural-classification.mjs --check` | PASS; unchanged 572 / 326 / 246 figure |
| `git diff --check` | PASS |

The new Math projector module reports two import-style warnings recommending
Lean's module syntax for its mathlib imports. No declaration warning originates
in the new GUT or Physics modules. Existing dependency/import deprecations,
module-syntax warnings and previously recorded lint warnings are replayed in
the aggregate build; none is suppressed or converted into an audit exception.

The root README, its input flow/result diagrams and classification table were
reviewed unchanged: this model-specific amplitude construction adds no new
main-claim interface or classification count. The ordinary-link navigation
is unchanged. The figure check confirms the retained generated asset.

The planned algebraic endpoint is complete. The source is not equated with an
analytic zero-mode solution: nonzero brane mixing changes the mode problem,
and analytic mixed-mode admission remains unproved. Subsequent authorized
parent integration has its own [merged-state verification](integration-verification.md).
No integration into master or remote publication is claimed.
