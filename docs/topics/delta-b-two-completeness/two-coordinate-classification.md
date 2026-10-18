# Two probes and intrinsic two-coordinate completeness

## Mathematical structure

The product invariant basis gives an array `c : Fin 5 → Fin 5 → ℂ` on the
actual domain `(Color ⊗ Spin)^6`. Species statistics requires a minus sign
under the up exchange `(0 2)` and the down exchanges `(1 3)`, `(3 4)`, `(4 5)`.
These four transpositions generate all 48 within-species permutations. The
full sign rule does not include up/down exchange.

For each generator, `colorMatrix` and `spinMatrix` are the separate 5-by-5
actions on the epsilon-product bases. Their identities are proved for
arbitrary vectors, not just probe inputs. The coefficient equation is

`cₚq + Σₐ Σ_b Aₚa B_qb cₐb = 0`.

The proof isolates these equations from invariance. Their solution is
`embed z`, with `z = (c₄₀, c₄₂)`:

```
[-2z₀, -z₀, -z₀-z₁, -z₀, -z₀+z₁]
[z₀+z₁, z₀+z₁, z₀+z₁, z₀+z₁, 0]
[-z₀-z₁, 0, -z₀-z₁, 0, 0]
[-z₀, -z₀, -z₁, -z₁, 0]
[z₀, 0, z₁, 0, 0]
```

`embed_statistics` verifies sufficiency. `kernel_reconstruct` verifies
necessity through 23 sparse rational row certificates. Each certificate is
checked in Lean; no external rank or spanning assertion is a theorem
parameter. The [stdlib script](../../../tools/delta-b-two/README.md) reproduces
the exact calculations but is not trusted by the proof.

## The two actual probes

Both evaluations use color indices `(0,0,1,1,2,2)`. Their spin indices are
respectively `(0,1,0,1,0,1)` and `(0,0,1,1,0,1)`, on decomposable quarks
`colorBasis i ⊗ weakBasis j`, in the ordered species pattern `(u,d,u,d,d,d)`.
On `reconstruct (embed z)` their values are `(z₀-z₁, z₁)`. Thus measured
coordinates `(t₀,t₁)` reconstruct via `z=(t₀+t₁,t₁)`.

The source provides both a linear equivalence of the equation kernel with
`ℂ²` and an equivalence of invariant species-alternating multilinear maps
with `ℂ²`. In particular, reconstruction is defined on arbitrary quark
inputs, not only decomposable inputs or a contraction ansatz.

## Intrinsic exterior sector

`Sector` is the pre-existing degree `(2,4)` submodule of physical
gauge/Lorentz invariant exterior coefficients. It is not redefined as a
contraction-generated image. Restriction maps it to the classified
multilinear space. The reverse construction linearizes a six-slot map on
the ordered tensor domain, derives physical invariance from independent
color/Weyl invariance and charge cancellation, and alternatizes with `1/48`.
The existing `2! 4! = 48` theorem proves restriction followed by this lift is
the identity. Degree-sensitive slot extensionality proves the other inverse.

`twoCoordinateEquiv` composes these equivalences. `finrank_sector` asserts
dimension two, while `probes_inverse` and `inverse_probes` expose the two
directions of the explicit inverse. The conventional Fierz identity remains
available, but it is not used as a spanning premise.

## Sources and verification

- [Species equations and probes](../../../Physics/StandardModel/Operators/SixQuarkSpeciesQuotient.lean)
- [Intrinsic inverse](../../../Physics/StandardModel/Operators/SixQuarkTwoCoordinates.lean)
- [Strict axiom audit](../../../Physics/StandardModel/Operators/Audit/AuditSixQuarkTwoCoordinates.lean)

Verification outcomes are recorded in the [topic record](README.md).
No new axiom, literature premise, dependency pin, resource-limit override,
audit exception, or physical-sector extension is introduced.
