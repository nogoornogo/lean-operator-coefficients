# Verification

- Working branch: `proof/sm-statistical-finite-kernel`.
- Target: `proof/su3-plane-generation` (bounded unmerged-parent exception).
- Verified commit hash is reported after commit creation.
- No merge or push performed.

## Focused proof checks

`lake env lean` checked each new proof module during development.
Final focused acceptance command:

    lake build Math.RepresentationTheory.Audit.AuditStatisticalFiniteKernel Physics.StandardModel.Operators.Audit.AuditSMStatisticalFiniteKernel

The Math audit checks the dependency layer and 17 declarations; the Physics
audit checks the layer and 19 declarations. Both use strict transitive axiom
collection and allow only `propext`, `Classical.choice` and `Quot.sound`.

An initial rewrite of the original-space iff reached the default deterministic
heartbeat limit. Explicit composition of the existing iff and bounded
existential transport resolved it; no resource setting was increased.
The first layout check identified the new Physics layer audit's missing
relocation-origin diagnostic; adding the existing ImportOrigin interface
resolved this without weakening its checks.

## Statement and scope review

The actual arbitrary-content Weyl theorem discharges affine, degree, image
surjectivity, Higgs-fixed and exhaustive-test inputs. Exact samples are real
natural numbers 0,...,n; the four real/imaginary off-diagonal families generate
the actual paired Weyl group. The finite carrier basis is classical; no group
test family is obtained merely by classical finite-dimensional selection.
The rank criterion is Weyl-only. The full local/original-space equivalence
retains actual gauge invariance explicitly; it is not a full finite matrix
or complete support classifier. Compact sampling stops at the recorded
SU(2) circle-factor/rational-chart certificate gate.

No `sorry`, custom axiom, audit exception, pin, dependency, resource-setting,
root README or unrelated user change was introduced.

## Final acceptance results

- Final focused build passed (4132 jobs): 17 Math and 19 Physics strict
  transitive axiom checks, with both layer checks; no warnings.
- One serialized `lake build` passed (6871 jobs), including Math/Physics/GUT
  aggregates. Disposable log: `/tmp/sm-statistical-finite-kernel-full-build.log`.
  No warning or error lines occurred in this full run.
- `node tools/layout/check-layout.mjs`: 1528 modules; layers, imports, cycles,
  aggregate coverage and relocation audits passed.
- `node tools/docs/check-links.mjs`: 810 Markdown files, 4994 local inline
  links, 94 heading fragments, zero errors.
- `git diff --check` and final staged diff check passed.
