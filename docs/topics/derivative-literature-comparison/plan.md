# Execution Contract

## Authority And Endpoints

The current instruction authorizes integration of the preceding helper and
creation of this topic's literature candidates and execution plan. That
planning checkpoint ends after source inspection, documentation checks and
a coherent commit. No comparison proof is claimed by this checkpoint.

The subsequent user instruction authorizes execution of the frozen six
[case contracts](cases.md). Process C1
through C6 in order, recording a terminal outcome for every case. Completion
means the portfolio was processed and its actual results reported; it does
not mean every hoped-for basis theorem was proved. Do not end execution
merely because one paper reached its stop or a milestone was committed.

## Common Assumptions

Work over complex exact algebraic sources with finite field labels and four
ordinary derivative directions, except C1's single direction. Preserve the
actual specified field and direction actions. Fix the leading equations
independently of the higher-dimension operators being tested. Use free
linear equations only where the case says so; use full differential closure
for nonlinear equations. IBP is the actual linear divergence range, not its
ideal closure. All candidates must descend through these actual relations.

The initial SMEFT tests are gaugeless specializations. Ordinary derivative
commutation does not prove a statement about noncommuting covariant
derivatives. A future covariant extension needs its own curvature, Bianchi,
matter-action and source dictionary; none is presumed by this plan.

Do not change public nonderivative APIs, pins, existing audits or import
boundaries. No analytic actions, S-matrix equivalence, all-order field
redefinition theorem, matching, RGE, nonperturbative QCD, rates or simulation
is part of the endpoint.

## Common Acceptance Gates

1. **Conventions.** Pin the paper version/location and the exact finite field
   content, derivative degree, leading equations and couplings. State signature,
   derivative normalization and factors of i; fix odd-field order, chirality,
   conjugation and flavor labels. Separate complex coefficient dimension from
   the real dimension of a Hermitian family. Verify the component dictionary
   before using the published expression as a test.
2. **Actual source and relations.** Enter through
   `Math.DerivativeInterface.graded` or `.equations`, or a proved connection
   from the existing linear-EOM source. For mixed linear equations, package
   the existing actual combined-relation/action construction into the common
   input if needed. No replacement by a guessed relation matrix is allowed.
   The helper is optional and generates equations from the separately fixed
   leading Lagrangian, not from the candidate under test.
3. **Selection.** For nonlinear EOM use full-source `Input.select` and its
   full relation preimage. Retain other field counts traversed by a relation.
   Do not truncate to a grade without proving the required equality.
   Restricting a global coefficient is not automatically surjective onto
   all selected invariant coefficients.
4. **Published expressions.** Prove equality of literal finite expressions
   with their actual-source images, relation annihilation, and the claimed
   extraction/reconstruction laws. Use actual group-equivariant coefficient
   maps. A displayed invariant operator is not automatically its own dual
   coefficient functional; prove that dictionary where used.
5. **Completeness.** A basis/count comparison additionally needs independent
   spanning and independence of the entire stated sector, via inverse laws
   or a sound and complete exact finite certificate. Do not assume invariants
   commute with quotient, a group-invariant complement exists, or a finite
   subgroup already detects the full group. Matching counts alone fails this gate.
6. **Controls.** Include the case's sign, normalization or off-shell control.
   Exercise `extraction` and `reconstruction` on the same candidates, and
   compare degree-zero input with `fromNonDerivative` wherever applicable.
   For a helper comparison identify its actual seed closure with direct EOM
   input, including any nonzero normalization factor.

Assertions about full-sector bases must pass all applicable gates. Literal
expression or relation certificates remain useful narrower results when
completeness is unresolved; label them as such.

## Reuse And Bounded Routes

Read only the sources needed by the current case. Existing entry points are
the [input guide](../derivative-interface-adapters/input-guide.md),
[linear EOM/IBP bridge](../../../Math/RepresentationTheory/LinearJetIBP.lean),
[helper guide](../local-lagrangian-helper/input-guide.md),
[complete scalar control](../../../Math/Algebra/ScalarJetQuadratic.lean),
[complete mixed control](../../../Math/Algebra/MixedJetQuadratic.lean),
[paired Weyl completion](../jet-eom-completion/results.md), and
[actual substitution](../../../Math/Algebra/JetFirstVariation.lean).
Their existence does not discharge the new invariant-span dictionaries.

For each missing bridge, try at most two named routes once:

- A structural proof using the existing actual representation, contraction,
  quotient and derivative APIs, decomposed into reusable small lemmas.
- B an exact finite-coordinate certificate, with its presentation and
  completeness proved against the same actual source. Scripts may generate
  or check candidate matrices; Lean checks their semantics and exact result.

Do not recursively start a general invariant solver or a new foundational
theory. On exhausting both routes, retain any verified narrower certificate,
record the precise gap and advance. Reuse a shared gap identifier so a failed
foundation is not silently retried from scratch for each paper. Still run
the next paper's independent gate and any available narrower comparison.

## Resource And Verification Policy

Retain default Lean heartbeat/recursion limits. Use at most two build threads,
a 16 GiB per-process address-space guard and 540-second per-invocation
wall-clock guard; final focused audits use a 180-second guard. These are
execution ceilings, not time estimates. Decompose a heavy proof within its
named route before declaring a resource stop; do not raise ceilings or
weaken a theorem/audit to make it pass. This policy bounds each attempted
route, not the total duration of a complete portfolio.

Register new sources and persistent strict transitive axiom/import audits in
the appropriate aggregate. At a coherent proof checkpoint run focused builds
and audits, then one serialized `lake build`, layout, topic navigation,
portable metadata, local links and `git diff --check`. Allowed Lean axioms
remain the existing standard ones. No `sorry`, custom axiom, enlarged audit
allowlist or paper-completeness parameter may establish success. Further
full builds are justified by new proof changes, not documentation edits.

At verified comparison milestones update the relevant proof dossier,
assumptions ledger and English [literature coverage index](../../verification/README.md)
with only the actual proved claim and its limitations. Pending targets stay
in this topic. Commit coherent verified milestones and continue the queue.

## Per-Case Stops And Advancement

| Terminal outcome | Required evidence | Next action |
| --- | --- | --- |
| Proved | Exact frozen contract and all applicable gates pass | Record result, then next case |
| Partial | Checked literal/relation/input result; missing completeness or other contract component named | Record narrower theorem and gap, then next case |
| Mismatch | Rechecked conventions/version and retained reproducible exact witness | Report the discrepancy without changing assumptions to hide it, then next case |
| Prerequisite stop | Needed bridge absent or beyond the bounded contract after permitted routes | Record what is unproved, then next case |
| Resource stop | Guard/Lean failure recorded and bounded routes exhausted | Preserve checked work, then next case |

`Pending` and `in progress` are not terminal. An unproved conditional
implication is not a proved comparison. After C6, report all six outcomes,
their common coverage and remaining gaps; do not automatically add the
background references or another flavor/degree range.

Only a genuinely global obstacle interrupts the whole queue: user stop,
unclear/dirty integration state, semantic conflict with another contributor,
or a required action outside existing authority such as a pin change. An
individual case's mathematical prerequisite or resource stop is local.
Merging this topic into master remains a separate user decision.
