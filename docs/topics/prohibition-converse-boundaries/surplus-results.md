# A Physical Counterexample to the Surplus Converse

The absence of joint Hom surplus does not imply prohibition in the original
arbitrary invariant symmetric-mass scope. The
[source](../../../Physics/FieldTheory/Mass/BalancedSpeciesSurplusControl.lean)
constructs a counterexample on actual SM gauge fields and their residual
external tensor factors.

Choose any finite-dimensional nontrivial residual representation s. In all
three species, source and target copy representations are the identical s.
Every tested residual r has equal source and target Hom multiplicities, so no
surplus is possible. Construct the field sum Q + uc + ec with invariant zero
mass, zero species copy maps and zero dual-field maps. The injective gauge-field
embeddings and all mass commuting squares are proved.

The zero-map kernels retain s. Explicit kernel splits, actual participating
range equivalences and the existing gauge/spin exterior alternation theorem
produce a nonzero participating light qque coefficient. Thus all three ranges
are genuinely light and the coefficient survives statistics. This is neither
a raw tensor nor an unsupported numerical tuple. No irreducibility or
semisimplicity of s is needed for this construction.

The theorem no_surplus is uniform in the tested r; physical_light_coefficient,
not_forbidden and converse_counterexample give the actual opposite outcome.
The [contract](surplus-contract.md) is complete. The original surplus theorem
is unchanged: positive joint surplus still guarantees a coefficient for every
admitted mass. The counterexample uses a degenerate mass permitted by that
scope, and is not an exact SM-spectrum construction or a full-rank-mass theorem.
