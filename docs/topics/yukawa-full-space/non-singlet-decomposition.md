# Non-Singlet Decomposition

Status: completed and verified; parent topic remains incomplete and unmerged.
Branch `proof/yukawa-full-space`, checkpoint `checkpoint 01`,
integration target `master`; parent full-coupling endpoint remains separate.

## Frozen Endpoint

Prove an actual SM x H representation equivalence for the whole light
radical: exterior-ten plus one dual-five if (a,b) is nonzero, or exterior-ten
plus a five and two dual-fives if a=b=0, together with the already identified
singlet kernel. Split ten/five/dual-five into the existing irreducible SM
constituents, with neutral H. Do not infer equivariance from dimension.

Implement the two-copy linear constraint as a reusable representation lemma,
then use actual equivariant branching, prove the mass/light-coordinate
correspondence, and compose explicit equivalences. No new physical premises,
scalar choice, group-theory foundations, pins or numerical inputs.

## Verification

- `lake build Math.RepresentationTheory.Audit.AuditTwoCopyKernel
  Physics.StandardModel.Audit.AuditTwistedFundamentalIrreducibility`: passed,
  6 generic and 5 irreducibility strict transitive axiom checks.
- `lake build GUT.SU6.Audit.AuditNonSingletSpectrum`: passed, 4271 jobs,
  18 strict transitive axiom checks. Only propext, Classical.choice and
  Quot.sound in all three audits.
- Full `lake build`: passed, 5874 jobs. No new-source warnings; existing
  dependency warnings replayed. Initial local proof errors were corrected.
- `python3 -m unittest discover -s tools/yukawa -p 'test_*.py'`: 8 passed,
  1.255 seconds. Scripts are cross-checks only, not theorem premises.
- `node tools/layout/check-layout.mjs`: passed, 823 modules.
- `node tools/docs/check-links.mjs`: 308 Markdown files, 1881 local links,
  33 heading fragments, zero errors. `git diff --check`: passed.
- Lean LSP unavailable; used targeted builds. No new web sources consulted.
  No dependencies, limits, axioms or audit exceptions changed. Qque scripts
  not rerun: their covered definitions are unchanged.

## Result

For every allowed actual Yukawa at the specified vacuum, let a,b be the
two five-pairing coefficients and K the kernel of [[u,v],[v,w]]. Put
k=dim K, which is 0, 1 or 2 by the existing exact rank criterion. Then,
as SM-cover x H representations with trivial H action:

| Coefficients | Entire light radical |
|---|---|
| a or b nonzero | T + F* + k trivial copies |
| a=b=0 | T + F + F* + F* + k trivial copies |

These are explicit equivariant equivalences, not character identities or
dimension counts. The surviving dual-five is a coefficient-dependent
linear combination of the two original copies. No division by a vanishing
coefficient is used: the equivalence branches on which coefficient is nonzero.

Here T and F denote the restricted ten and five blocks, NOT irreducible
representations of the residual group. Their irreducible factors, writing
the integer charge q=6Y, are:

| Block | Factors (SU3, SU2, q) |
|---|---|
| T | (bar3,1,-4), (3,2,1), (1,1,6) |
| F | (3,1,-2), (1,2,3) |
| F* | (bar3,1,2), (1,dual2,-3) |

The formal target retains the dual weak carrier; no unproved identification
of it with a chosen lepton basis is needed. The charged one-dimensional
factor in T is not a trivial singlet. The k copies use the pre-existing
`trivialCopiesEquiv` and `scalar_irreducible` results.

## Implementation

- [TwoCopyKernel](../../../Math/RepresentationTheory/Decomposition/TwoCopyKernel.lean):
  arbitrary-group equivariant solution of a z=b z=0 and a f+b g=0.
- [TwistedFundamentalIrreducibility](../../../Physics/StandardModel/Gauge/TwistedFundamentalIrreducibility.lean):
  color and weak factors at any integer hypercharge, their duals, and
  preservation of irreducibility under neutral H extension.
- [NonSingletCoordinates](../../../GUT/SU6/Yukawa/NonSingletCoordinates.lean):
  actual equivariant branching and coordinate/constraint correspondence.
- [ResidualConstituents](../../../GUT/SU6/Yukawa/ResidualConstituents.lean):
  dual-product equivalence and all seven constituent irreducibility proofs.
- [NonSingletSpectrum](../../../GUT/SU6/Yukawa/NonSingletSpectrum.lean):
  `radicalEquiv`, `nonzeroDecomposition`, `zeroDecomposition` and the
  all-coupling endpoint `all_yukawa_decompositions`.
- [Model audit](../../../GUT/SU6/Audit/AuditNonSingletSpectrum.lean),
  [generic audit](../../../Math/RepresentationTheory/Audit/AuditTwoCopyKernel.lean),
  [irreducibility audit](../../../Physics/StandardModel/Audit/AuditTwistedFundamentalIrreducibility.lean).

Large analytic equivalences initially caused deterministic kernel timeouts
when unfolding through nested projections. The final proofs use small
coordinate lemmas and opaque chosen equivalences with proved equalities to
the original constructions. These are proved interfaces, not new assumptions
or imported computational answers. No heartbeat increase was used.

## Boundary

The non-singlet decomposition endpoint is closed.
The fixed vacuum, zero bare mass, actual 15+2 bar6 matter, nonminimal
symmetric-form scalar and neutral H are unchanged. This does not select a
vacuum from a potential, classify other Higgs choices, prove a decay
amplitude or complete the 22-dimensional coupling space. The last remains
the parent topic's outstanding endpoint, so this branch is not merged yet.
