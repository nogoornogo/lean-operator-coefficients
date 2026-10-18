# SC-3: Standard-Chain Recovery

Status: Lean-checked. The concrete positive control is closed; the negative
triality control remains in SC-4.

[ConjugationAdapter.lean](../../../GUT/Common/StandardChain/ConjugationAdapter.lean)
uses namespace `GUT.StandardChainConjugation`.

`realizes i p` takes the actual signed permutation representative in SU(5)
and maps it through the supplied homomorphism i. Homomorphism laws transport
`MaximalTorus.hom_conjugate` to the required ambient identity.
`threeConjugations i` selects precisely the three planned permutations.
No character invariance or desired charge equality is a construction input.

`restrict_eq`, `mass_eq` and `spectrum_eq` preserve the original restricted
representation, symmetric bilinear mass and resolved radical spectrum exactly.
The equality is definitional, not just agreement of dimensions or dual indices.
`hasTarget` therefore reuses the old light target without strengthening it.

`profiles_compatible`, `actual_signature_pair` and `selection_rule_obstruction`
now recover the old consumers **through the new structural theorem**, without
invoking the old selection-rule proof. `continuous_selection_rule_obstruction`
accepts the existing continuous model unchanged; no new continuity, injectivity,
or full-G-invariant mass requirement is introduced.

This covers every supplied SU(5)-to-G chain in the existing interface. It is
not a new classification of embeddings or a new proof that all G admit such
a chain. Existing SU(N), Spin and E6-candidate applications inherit the adapter;
the named-E6 literature boundary is unaffected.

## Verification

```sh
lake build GUT.Common.StandardChain.Audit.AuditConjugationAdapter
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

Focused build: 3925 jobs, 12 strict transitive axiom checks passed. Full build:
5562 jobs. Layout: 546 modules, no errors. Link and diff checks passed before
commit. New files have no warnings; prior warnings remain.

The [audit](../../../GUT/Common/StandardChain/Audit/AuditConjugationAdapter.lean)
checks preservation of the actual mass form, radical and spectrum, and retains
the original joint continuity alongside the new conclusion. `finite_benchmark`
instantiates the endpoint on the actual 15-dimensional SU(5) model with arbitrary
residual characters of `Multiplicative (ZMod 3)`. Its radical dimension is proved
15, so the positive control is not an empty-matter implication.

The allowlist remains only `propext`, `Classical.choice`, `Quot.sound`. General
Physics import exclusions remain independently enforced by the SC-1/2 audits.
