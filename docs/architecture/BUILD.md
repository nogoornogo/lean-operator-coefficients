# Building And Verification

Install Git, [elan](https://github.com/leanprover/elan), and a C/C++ build
toolchain supported by Lean. Initial setup needs network access and ample disk
space for Lean, dependencies and compiled artifacts. Run commands from the
repository root so elan selects the committed toolchain, not your global default.

Ensure `elan`, `lake` and `lean` are available on PATH. Documentation examples
use relative paths or explicit placeholders, not a particular user's checkout.

Replace `<repository-url>` with the URL or Git bundle supplied by the maintainer;
this checkout does not configure a public hosting URL.

```sh
git clone <repository-url> project-checkout
cd project-checkout
lake exe cache get
lake build
```

`project-checkout` is an arbitrary local directory name, not a project title.
The committed `lean-toolchain` pins Lean **4.35.0-rc3**; `lakefile.lean` and
`lake-manifest.json` pin mathlib and TauCeti. Keep those files unchanged for
reproduction; do not run `lake update` as a routine build step. Mathlib's cache
reduces compilation work but does not supply all project/TauCeti artifacts.

`lake build` includes the persistent audits through the `Math.lean`,
`Physics.lean` and `GUT.lean` aggregates. To replay a
focused audit after building, for example:

```sh
lake env lean Physics/StandardModel/Operators/Audit/AuditLightSMSpeciesQque.lean
```

The [implementation index](../proof/INTERFACES.md) records verified full-build
checkpoints. A recorded local build is not a fresh-clone reproduction test.
Optional [API documentation](../architecture/DOCUMENTATION.md) uses the separate
`docbuild/` project; doc-gen4 is not required for proof builds.
The [external finite-certificate tools](../../tools/e6/README.md) have separate tests
and are not trusted proof oracles.
