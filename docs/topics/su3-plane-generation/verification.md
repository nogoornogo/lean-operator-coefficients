# Verification

- Branch: `proof/su3-plane-generation`.
- Target: `proof/sm-local-invariant-kernel`; bounded unmerged-parent exception.
- Verified commit hash is reported after commit creation, not self-embedded.
- No integration or remote push performed.

## Proof checks

`lake env lean Math/LieGroups/SpecialUnitary/PlaneGenerationThree.lean`
passed, without warnings.

`lake build Math.LieGroups.SpecialUnitary.Audit.AuditPlaneGenerationThree`
passed (3135 jobs). The persistent audit checks the Math dependency layer and
14 declarations' strict transitive axioms, allowing only `propext`,
`Classical.choice` and `Quot.sound`.

One serialized `lake build` passed (6863 jobs). Disposable output is at
`/tmp/su3-plane-generation-full-build.log`, outside source control. No warning
or error lines occurred in this run.

`node tools/layout/check-layout.mjs` passed: 1520 modules, layers, local
imports, cycles, aggregate coverage and relocation audits OK.

Final `node tools/docs/check-links.mjs` and `git diff --check` passed.
The first documentation check preceded this verification file and reported
its missing link; creation of this file resolved that expected interim error.

## Statement review

The group is the actual special unitary matrix submonoid with its existing
group structure. The plane family fixes a coordinate column; unitarity fixes
the corresponding row. The decomposition is algebraic and has three factors.
There is no continuity, finite-dimensional-representation, generating-family,
external literature or complexification assumption in the generation theorem.
Its invariant consumer takes an arbitrary complex representation and scalar
linear functional. Infinite plane parameters remain; no finite sampled
statistical-source claim is made.

No `sorry`, custom axiom, audit exception, dependency/pin, resource-setting or
root README change was introduced. No unrelated worktree changes were present.
