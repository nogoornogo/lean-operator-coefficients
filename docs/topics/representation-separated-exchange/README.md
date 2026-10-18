# Representation-Separated Mediator Exchange

- ID: representation-separated-exchange
- Status: completed
- Result type: proved representation-theoretic sufficient conditions and conditional SU(5) inheritance.
- Working branch: `proof/representation-separated-exchange`.
- Integration target: `master`.

## Frozen Endpoint

Derive the support and mass identities used by
[mediator inheritance](../mediator-inheritance/README.md) from equivariance
and absence of common irreducible constituents. Retained and additional
mediators have a supplied equivariant product decomposition. Use existing
semisimplicity/common-constituent results, not new compact-group foundations.

Two bounded routes: source support from the absence of constituents shared
by the source and added mediator; dual-current support from the corresponding
absence for the added dual representation. Derive forbidden mass blocks by
the same method. Where possible construct the retained invertible mass from
the full equivariant mass and its inverse rather than assuming invertibility
of an arbitrary diagonal block. Connect to the existing qque sector and
give a conditional SU(5)-core application.

Inputs are equivariance, the specified representation split, semisimplicity
of each source used in a no-map argument, and actual no-shared-constituent
conditions. Retained current and mass identification with SU(5) remain model
inputs. Do not assume zero unwanted blocks or nonzero full exchange as an
alternative to deriving them. No assertion for repeated isomorphic summands,
arbitrary group inclusions, arbitrary vacua or amplitudes is authorized.
If extra foundations are required, stop and record that boundary.

## Source Interfaces

- [Common constituents](../../../Math/RepresentationTheory/Decomposition/CommonIrreducible.lean)
- [Equivariant products and dual restriction](../../../Math/RepresentationTheory/Decomposition/SplitRepresentationProjection.lean)
- [Mass and current inheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)
- [Qque inheritance](../../../Physics/StandardModel/Operators/QqueMediatorInheritance.lean)
- [Retained SU(5) application](../../../GUT/SU5/Matching/InheritedExchange.lean)

## Acceptance

Focused builds, persistent strict transitive axiom audits, full `lake build`,
layout/link/diff checks and exact qque regressions. Lean LSP is unavailable;
use source reads and builds. No new axioms, `sorry`, dependency or heartbeat
changes. Commit and merge verified work into master with `--no-ff`, recheck,
retain the branch and do not push.

## Results

### Derived Conditions

[SeparatedMediator](../../../Math/RepresentationTheory/Decomposition/SeparatedMediator.lean)
uses the existing `CommonIrreducible.all_zero_iff`: if the source is semisimple
and shares no actual irreducible constituent with the target, every
intertwining map between them is zero. The source is always identified
explicitly; semisimplicity of an unrelated representation is not sufficient.

For retained r, additional s and source representation a, it proves:

| Separation and semisimplicity | Derived identity |
| --- | --- |
| r semisimple, no shared constituent of r and s | Any equivariant endomorphism preserves `(x,0)`; its r-to-s mass block is zero. |
| s semisimple, no shared constituent of s and r | Projection to r commutes with the retained block; the s-to-r mass block is zero. |
| a semisimple, no shared constituent of a and s | A current `a -> r + s` is supported on r. |
| a semisimple, no shared constituent of a and `s.dual` | A current `a -> (r + s).dual` annihilates s and factors through projection to r. |

The retained mass `coreMass` is constructed as an equivariant linear
equivalence. Under the first row, both N and its equivariant inverse preserve
r; their retained blocks are mutual inverses. Thus invertibility of the
retained block is derived, not inferred incorrectly from invertibility of
an arbitrary full matrix. No finite-dimensionality or positivity is required
for this algebraic step. Topology and compactness are not added as hypotheses.

### Exchange And Qque

[SeparatedMediatorQque](../../../Physics/StandardModel/Operators/SeparatedMediatorQque.lean)
connects these derived identities to the previous exchange construction.
The current representations are the full tensor products `q tensor u` and
`q tensor e`, not merely the individual species. It proves exact equality of
the full and retained ordered coefficients and of their generated qque
sector elements, including alternation.

The source route uses separation of r from s and of `q tensor u` from s.
The observer route uses separation of `q tensor e` from `s.dual`, s from r,
and also r from s to use the same constructed `coreMass`. Each no-map argument
requires semisimplicity of its source. Both currents and the full mass are
equivariant in this generic API. Its nonzero-transfer lemma takes only the
retained nonzero sector as a premise, never a nonzero full exchange.
Existing Hom classification applies to the equal sector elements unchanged.

### Conditional SU(5) Application

[SeparatedExchange](../../../GUT/SU5/Matching/SeparatedExchange.lean) provides
two SU(5)-core endpoints. An auxiliary symmetry H acts on the retained
six-channel space, additional mediators, and the relevant current-source
tensor. Full mass equivariance, constituent separation and current
equivariance derive the support and mass identities used by inheritance.
The previous nonzero SU(5) exterior coefficient is then recovered exactly.

The retained mass value and retained current maps must still be identified
with the checked SU(5) data; these are not derived from separation alone.
Only the current used in the no-map argument needs auxiliary equivariance
in these wrappers. Full SM invariance follows from the derived equality to
the existing SU(5) coefficient. The observer wrapper can use the already
invertible SU(5) mass, so it does not additionally require the hypotheses
used to construct the generic `coreMass`.

### Limits And Control

These are structural sufficient conditions, stronger than allowing a
particular coupling to vanish accidentally. They are not necessary conditions
or a classification of all nonzero exchanges. No specific larger GUT's
auxiliary symmetry, branching data, no-shared-constituent predicates or
retained-block identifications have been verified in this topic.
The result reduces those applications to representation and retained-data
checks; it does not automatically discharge them for SU(N), Spin or E6.

The repeated-summand control `repeatedSwap` is an invertible equivariant map
on `r + r` that moves the first summand to the second and has zero retained
block. It checks why symmetry alone cannot suppress mixing between equivalent
copies or justify arbitrary mass restriction. This is an algebraic control,
not a positive physical mass-squared operator or a new GUT counterexample.

Stop here: both bounded routes are closed. No new UV action, vacuum selection,
Grassmann reordering, energy hierarchy or amplitude result is claimed. Further
application should supply genuine model symmetries and representation data,
not introduce a hypothesis of nonzero generated exchange.

### Verification

- Focused build of the three new audit modules passed: 10 Math, 5 Physics,
  2 SU(5) declarations checked transitively. Only `propext`, `Classical.choice`,
  `Quot.sound` are allowed. New proof files have no warnings.
- Full `lake build`: passed, 5797 jobs. Existing warnings were replayed;
  new proof files had no warnings. Repeat the build after integration.
- `node tools/layout/check-layout.mjs`: passed, 746 modules.
- Local link and `git diff --check` inspections before and after integration.
- Exact qque regressions passed: `python3 tools/qque/audit_one_generation.py`
  (4 tests), `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3).
  These check existing finite conventions, not new larger-model realizations.
- No existing proof, dependency pin, heartbeat limit or axiom policy changed.
  Git ancestry records topic/merge commits; retain the branch and do not push.
