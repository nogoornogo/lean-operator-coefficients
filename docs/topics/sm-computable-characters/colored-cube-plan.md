# Middle colored exterior cube

Resume `proof/sm-computable-characters` from `checkpoint 01`, integration target
`master`. The user requests continued remaining proofs. No merge or push,
pins, numerical rank/multiplicity proofs or new external premises.

## Frozen construction

Target the actual SU3 defining color tensor SU2 spin doublet:

```text
Lambda^3(3 tensor 2) = Sym^3(2) direct-sum (trace-free End(3) tensor 2).
```

Do not assume adjoint irreducibility, this equivalence or positivity. First
construct the universal color hook K = ker(V tensor Lambda^2 V -> Lambda^3 V).
Use exterior multiplication and its three-slot coproduct, with W*delta=3*id.
The resulting projection onto K is equivariant. For dimension-three color,
identify its kernel with the actual trace-free endomorphisms by the proved
Lambda^2(color) = dual(color) map and tensor/Hom equivalence.

For the spin doublet, construct a cubic contraction G using the invariant
alternating spin pairing and color hook terms. Construct J from the spin
volume bivector and the color exterior-square section. Prove G*J=9 times
the hook projection and that G kills the top color-column Sym^3(spin).
These identities must hold for arbitrary color vectors, not checked on a
large exterior basis. A six-term three-slot alternating identity is allowed
as universal algebra, independent of contents or representation dimensions.
Use these actual maps for independence/completeness; any dimension reasoning
must stay structural, not a table of evaluated ranks or multiplicities.

## Order and boundaries

Implement and audit the hook exterior maps first, then spin contraction,
then actual color identification and full cube consumers. Preserve separate
spin factors and semisimple/charge boundaries in Physics adapters. The Q
core and general compatible positive color coupling remain subsequent
obligations, not assumptions of this construction. If a required identity
fails, investigate its normalization and signs; no new axiom or unknown Hom
may substitute for it.

Focused guarded builds: one Lean thread, 6 GiB RSS, 4 GiB available reserve,
300 seconds. Full serialized aggregates use the established 10 GiB guard.
Run strict transitive audits, full `lake build`, layout/link/retired-certificate
and diff checks, and commit coherent verified milestones while continuing.

## Result

The frozen U/D and conjugate cube construction is proved; see
[results](colored-cube-results.md) and [verification](colored-cube-verification.md).
The final completeness step uses standard functor dimension formulas after
explicitly proving independence of both embeddings. No content rank or
multiplicity is evaluated. The Q-core and general color coupling interfaces
remain outside this completed bounded construction.
