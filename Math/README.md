# Mathematics

Mathematical results organized by field: linear algebra, representation theory,
Lie algebras, concrete Lie groups and topology. This layer imports neither
Physics nor GUT. mathlib and TauCeti remain pinned external dependencies.

Math-owned declarations now use `Math.*`, matching the import-layer ownership.
The migration does not provide old `GUT.*` aliases or designate an upstream
destination. Import paths remain unchanged. See the
[declaration migration](../docs/topics/math-namespaces/README.md).
See the [layout and checks](../docs/architecture/MODULE_LAYOUT.md),
[upstream policy](../docs/architecture/UPSTREAMING.md), and the
[E6 literature boundary](../docs/proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).
