# Shared Physics

Finite-dimensional invariant mass/Yukawa algebra and shared Standard Model
gauge tensors, spectra and operator signatures. This layer may import Math
but not GUT. Concrete unification-model adapters belong to GUT instead.

Existing declaration namespaces are preserved; import paths begin with `Physics`.
See the [layout](../docs/architecture/MODULE_LAYOUT.md),
[scope](../docs/proof/current/applications/GUT/SCOPE.md), and
[shared selection rules](../docs/proof/current/applications/Physics/SHARED_SELECTION_RULES.md).

The [actual triality counterexample](../docs/topics/group-independent-assumptions/spectrum-bridge.md)
tests the necessity of UV structure using only shared SM matter, torus
characters and an invariant mass sector; it imports no GUT application module.
