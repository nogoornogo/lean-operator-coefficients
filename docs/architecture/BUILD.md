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
The committed `lean-toolchain` pins Lean **4.35.0**; `lakefile.lean` and
`lake-manifest.json` pin Mathlib, TauCeti and Physlib. Keep those files unchanged for
reproduction; do not run `lake update` as a routine build step. Mathlib's cache
reduces compilation work but does not supply all project/TauCeti artifacts.
The combined project passes its [v4.35.0 compatibility gate](../topics/derivative-ibp/verification.md),
including all three aggregates and their persistent audits. The Physlib
connection covers the selected algebra sources; larger external jet/analytic
packages and optional HTML generation are outside that build claim.

`lake build` includes the persistent audits through the `Math.lean`,
`Physics.lean` and `GUT.lean` aggregates. To replay a
focused audit after building, for example:

```sh
lake env lean -j2 Physics/StandardModel/Operators/BaryonOne/Qque/Audit/AuditLightSMSpeciesQque.lean
```

The root package passes `-j2` to Lean through Lake's `weakLeanArgs`, limiting
each root-module compiler's task manager to two threads without changing proof
options or dependency pins. `lake env lean` needs the flag explicitly.
`LEAN_NUM_THREADS=2` alone does not configure Lean 4.35's shell; it is not a
substitute for this flag. This limit does not cap Lake's number of simultaneous
compiler processes or alter external packages' compiler arguments.

The [implementation index](../proof/INTERFACES.md) records verified full-build
checkpoints. A recorded local build is not a fresh-clone reproduction test.
Lake's incremental builds may reuse existing project artifacts and replay saved
audit output. Successful `lake build` therefore does not show that every source
was elaborated again under the current resource limits. For per-module memory
measurements, use the [isolated source-compilation audit](../topics/proof-memory-audit/README.md),
which records actual compiler invocations and distinguishes fresh compilation
from reuse of its own measured artifacts. Pinned external package/toolchain
artifacts remain reusable inputs to that audit.
Optional [API documentation](../architecture/DOCUMENTATION.md) uses the separate
`docbuild/` project; doc-gen4 is not required for proof builds.
The [external finite-certificate tools](../../tools/e6/README.md) have separate tests
and are not trusted proof oracles.
