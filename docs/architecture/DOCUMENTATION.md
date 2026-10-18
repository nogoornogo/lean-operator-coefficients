# Generated API documentation

For setup and proof verification, see [Building and verification](BUILD.md).
This page concerns optional API generation, not the project result overview.

The project uses `doc-gen4` through the isolated Lake project in `docbuild/`.
It is intentionally not a dependency of the root proof package: ordinary
proof builds continue to use only the dependencies declared in
`lakefile.lean`.

The `doc-gen4` revision follows the root Lean toolchain and is pinned in
`docbuild/lakefile.toml`.  After changing the root dependencies, synchronize
the nested manifest from `docbuild/`:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake update operator-completeness
```

Generate the API documentation with:

```sh
DOCGEN_SRC=file lake build Math:docs Physics:docs GUT:docs
```

Run these commands from `docbuild/`.  The current generator documents the
transitive import closure, including Mathlib, rather than only declarations
owned by this repository.  Check available disk space before a full run; the
generator executable can be tested independently with `lake build doc-gen4`.

The source-layout migration changed module URLs; previously generated pages are
stale until regenerated. The layout change does not rename Lean declarations.
Documentation generation is optional and is not run as part of a source move.

The generated site is written below `docbuild/.lake/build/doc/` and is not
tracked by Git.  Serve that directory over HTTP when using search and other
dynamic features.  Generated documentation is a navigation aid; the audit
modules check proof dependencies; theorem dossiers state claims and hypotheses,
and topic records own verification and integration status. See the
[current proof guide](../proof/README.md). The
[retained dependency explanation](../topics/proof-program-context/proof-dependencies.md)
is context for its named proof routes, not a current proof-status authority.

For day-to-day declaration search, type inspection and proof-state feedback,
use the complementary [source search and Lean LSP workflow](LEAN_TOOLING.md).
