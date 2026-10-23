# Formalization architecture

This directory records the semantic organization of the formalization.  It is
deliberately independent of the order in which the original proof was
discovered.

The source tree is organized around three ownership levels:

1. `Math/` contains mathematics organized by field, including concrete Lie
   groups and topology. Upstream candidates are assessed file by file.
2. `Physics/` contains shared field theory and Standard Model spectra/operators.
3. `GUT/` contains common GUT theorem consumers and group-specific applications.

Imports point from applications to shared physics/mathematics, never backwards.
Canonical namespaces follow declaration ownership; subject namespaces need not
repeat the full file path. The [layout](MODULE_LAYOUT.md) records placement,
compatibility rules and automated checks.

The old labels A--E are retained only in the migration table and historical
records.  Active modules and proof documentation use semantic names.

- [Current proof guide](../proof/README.md) and [topic outcome guide](../topics/_history/README.md)
- [Retained proof-route explanation](../topics/proof-program-context/README.md)
- [Topic and branch workflow](WORKFLOW.md)
- [Literature verification coverage](../verification/README.md)
- [Module layout](MODULE_LAYOUT.md)
- [Structural proof policy](PROOF_ENGINEERING.md)
- [README figure and table maintenance](WORKFLOW.md#readme-figures-and-tables)
- [Generated API documentation](DOCUMENTATION.md)
- [Upstream contribution workflow](UPSTREAMING.md)

- [Distribution and attribution](DISTRIBUTION.md)
