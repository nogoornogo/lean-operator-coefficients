# Balanced Species Extensions

- ID: balanced-species-extension
- Status: completed
- Checkpoint detail: completed. Started/completed: stage 01.
- Working branch: `proof/balanced-species-extension`.
- Integration target: `master`.

## Frozen Endpoint

Derive positive automatic species support and actual qque exterior descent
for a light spectrum extending an exact-SM reference source. The reference
retains positive generations, two actual conjugations and T-unitarity.
The sources share compact H and compatible SM x H actions. The new action
is jointly continuous; the API needs no separate reference-continuity input.

The extension is specified by actual H-equivariant multiplicity decompositions:
for each of Q, up-left and electron-left, the new multiplicity and the dual
opposite multiplicity are the corresponding reference multiplicities plus
the SAME additional finite-dimensional H representation. Derive index
cancellation, not assume the character identities or positive support.

This is a species-local spectral sufficient condition. Merely SM-vectorlike
particle counts do not supply it. Automatically deriving these decompositions
from an arbitrary full SM x H self-dual summand is outside this bounded task.
No new dynamics, dependency changes or E6 topology work.

## Plan And Acceptance

1. Algebraic balanced-extension cancellation and identity/composition controls.
2. Transfer exact-reference index positivity into the new automatic presentation.
3. Connect to existing actual alternating/exterior endpoints.
4. Strict axiom audits, focused/full builds, layout/link/diff checks.

Stop if the existing character and extraction interfaces cannot close this
package without new theorem-level assumptions. Do not claim arbitrary
vectorlike additions preserve a signed index.

## Result

Proved the frozen species-local extension package. Actual H-equivariant
decompositions imply index cancellation; the exact reference then supplies
shared and pairwise positive support in the new automatic presentation.
The actual alternating and exterior endpoints follow without an exact
spectrum, conjugators or T-unitarity on the new radical.

Identity extensions recover the prior sufficient package. Cancellation is
transitive, and a positive Q addition provably excludes every old exact
SM-plus-singlets spectrum. This last fact is conditional on the extension
certificate, not a new nonzero-extra ambient model witness.

- [Statement, inputs and boundaries](../../proof/current/applications/Physics/BALANCED_SPECIES_EXTENSION.md)
- [Cancellation and controls](../../../Math/RepresentationTheory/Multiplicity/BalancedMultiplicityExtension.lean)
- [Positive support](../../../Physics/StandardModel/Spectrum/BalancedSpeciesExtension.lean)
- [Actual exterior coefficient](../../../Physics/StandardModel/Operators/BalancedSpeciesQque.lean)

The finite deliverables are closed. Automatic construction of the spectral
certificates from a global vectorlike summand and a nonzero-extra concrete
source remain outside this task, not completed work. Git ancestry records
the topic commit and no-ff integration into master; retain the branch.

## Verification

- Focused build of `Math.RepresentationTheory.Multiplicity.Audit.AuditBalancedMultiplicityExtension`
  and `Physics.StandardModel.Operators.Audit.AuditBalancedSpeciesQque`: passed,
  3999 jobs. Twelve strict transitive axiom checks and import-layer audits.
- `lake build`: passed, 5725 jobs. Existing dependency warnings remain;
  no new source warnings, sorry, axioms, heartbeat or dependency-pin changes.
- `python3 tools/qque/audit_one_generation.py`: four exact controls passed.
- `python3 tools/qque/audit_pairwise.py`: three exact controls passed.
  These check the reused contraction, not arbitrary added particle models.
- `node tools/layout/check-layout.mjs`: 680 modules, passed.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.
- Lean LSP MCP unavailable; used source inspection and Lean builds.

During development, a misplaced structure field and the comment/`omit`
ordering failed compilation and were corrected. The opposite-multiplicity
control needed an explicit definitional type change before arithmetic; no
extra hypothesis was introduced. Disposable build logs remain outside Git.
