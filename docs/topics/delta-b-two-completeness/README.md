# Delta-B = 2 all-right coefficient completeness

## Record

- ID: delta-b-two-completeness
- Status: completed
- Checkpoint detail: completed; intrinsic degree `(2,4)` two-probe equivalence proved
- Integration target: `proof/delta-b-two`
- Working branch: `proof/delta-b-two-completeness`
- Branch relation: bounded child of the then-unmerged `delta-b-two` topic;
  integrated into that parent by `checkpoint 01`. The user subsequently authorized
  the parent's integration into `master`; Git ancestry records that integration.

## Frozen scope

Formalize the one-generation, derivative-free, all-right-handed
`uudd dd` coefficient sector only.  The endpoint is an intrinsic exterior
degree `(2,4)` sector together with a proved two-coordinate description.  The
work must include:

1. restriction to the ordered `(u,d,u,d,d,d)` slots and reconstruction with
   the explicit `2! 4! = 48` normalization;
2. a classification of the relevant six-color contractions;
3. the Weyl-pairing Schouten identities and the resulting Fierz relation;
4. two independent probes and a proved inverse/reconstruction theorem.

The words *classification* and *completeness* mean spanning statements for the
specified invariant sector, not merely a list of conventional contractions.
No additional flavor, chirality, derivative or electroweak-doublet sector is
included.

## Boundaries and stop condition

- No RGE, nonperturbative QCD matrix elements, lattice input, oscillation-rate
  prediction or large numerical simulation.
- No `sorry`, new axiom, audit exception or unrecorded literature premise.
- Existing finite coordinate calculations are acceptable when they produce
  kernel-checked proofs and remain repository-scale.
- Stop with a documented negative feasibility result rather than label a
  contraction ansatz as the full invariant sector if either color or Weyl
  spanning cannot be proved with the available exact interfaces.

## Verification

### Degree `(2,4)` bridge

Implemented an intrinsic bidegree sector, proved that pure
`(u,d,u,d,d,d)` slots determine it, and constructed restriction back to an
ordered invariant.  Full alternatization of the restricted coefficient is
proved to be `2! 4! = 48` times the original slot value, so multiplication by
`1/48` gives a genuine reconstruction theorem.  This phase is independent of
the color and Weyl contraction ansatz.

Focused build and strict transitive axiom audit pass. Subsequent standalone
color/Weyl classifications and the combined two-probe inverse are recorded below.

### Exact contraction relations

Implemented the paper's `SSS` and `AAS` tensors in its stated index order and
proved their three pair-exchange symmetries and `SU(3)` invariance.  The Weyl
epsilon pairing satisfies the kernel-checked Schouten identity.  With the
fermionic sign needed to translate `O¹` into the repository's interleaved
slot order, the 48-term block alternatization now proves exactly

`O²_RRR - O¹_RRR = 3 O³_RRR`.

This is an exterior/statistics statement: the analogous pointwise equality
of the three unalternated ordered polynomials is false.  The proof explicitly
uses the two up permutations and all 24 down permutations; it does not invoke
dimensional regularization or a renormalization-scheme premise.

## Invariant-spanning phase

The right-Weyl half is implemented. A diagonal `SL(2,C)` element kills
the 44 basis coordinates whose numbers of zero and one indices are unequal;
a shear supplies 15 exact four-term relations among the remaining 20
coordinates.  Kernel-checked rational certificates reconstruct all 20 from
five probes, giving spanning by the five noncrossing epsilon pairings.  A
sixfold basis-extensionality theorem makes this a tensor-level result.  The
strict transitive axiom audit passes.

The color half now has a structural proof and a five-coordinate uniqueness
API. Weights restrict support to balanced tuples; signed color exchanges
reduce them to fifteen partitions into pairs. One four-slot rotation gives a
common three-term relation, and ten slot permutations reconstruct every
representative from five probes. The five epsilon products are invariant and
have an explicit triangular probe inverse. Subtracting the reconstruction
proves spanning of arbitrary invariant multilinear maps on arbitrary vectors,
as well as uniqueness of all five coefficients.

See [the six-color proof structure](six-color-classification.md) for the
mathematical argument, the ten readable relations, and the exact boundary of
the finite combinatorial checks. The rejected 85-step elimination draft was
replaced; it is not used as a premise or a checked proof baseline.

The classifications are now combined on the actual quark-slot tensor domain.
Arbitrary physical invariants have a unique 5-by-5 product coordinate array,
with a proved formula on decomposable inputs and tensor-basis extensionality
on all inputs. The exterior restriction satisfies physical invariance and
the species sign rule. These coordinates separate intrinsic degree `(2,4)`
coefficients. See [the combined-domain proof](color-weyl-bridge.md).

The species-statistics equations now have an explicit two-dimensional kernel.
Two actual quark evaluations give a linear equivalence on the invariant
species-alternating multilinear space and, via the `1/48` alternating lift,
on the entire intrinsic degree `(2,4)` exterior sector. Both inverse identities
and dimension two are proved without a spanning/rank premise. See
[the two-coordinate proof](two-coordinate-classification.md) and
[the classification boundary](classification-boundary.md).

### Two-coordinate verification and integration

- Focused builds of `SixQuarkSpeciesQuotient`, `SixQuarkTwoCoordinates`,
  `AuditSixQuarkTwoCoordinates`, and the existing `AuditSixQuarkInvariant`
  pass. The new audit has 23 strict transitive checks; the existing audit's
  18 checks still pass. Only `propext`, `Classical.choice`, and `Quot.sound`
  are permitted. The new sources and audit have no residual warnings.
- Exact stdlib certificate reproduction passes; Lean checks the deductions
  independently. No dependency pins or resource limits were changed.
- `lake build` passes (5950 jobs); existing dependency warnings are unchanged.
  Layout checks pass for 897 modules. Documentation checks pass for 337 files
  and 2042 local links; the read-only link checker required an unsandboxed
  retry after its sandboxed `git` subprocess returned `EPERM`.
  `git diff --check` passes.
- The child milestone `checkpoint 02` was integrated into `proof/delta-b-two` by
  `checkpoint 01`. The parent's integration target is `master`, with explicit user
  approval; merge `checkpoint 03` completes it. Post-merge verification is in the
  [parent record](../delta-b-two/README.md). This does not change the child's
  recorded integration target.

### Six-color verification

Targeted elaboration of the classification and inverse identities passed.
The following checks passed on the working branch:

- `lake build Physics.StandardModel.Gauge.SixColorInvariant
  Physics.StandardModel.Gauge.Audit.AuditSixColorInvariant`: 13 persisted
  strict transitive axiom checks, permitting only `propext`, `Classical.choice`
  and `Quot.sound`. The new source and audit have no residual warnings.
- `lake build`: successful, 5944 jobs; existing dependency warnings are unchanged.
- `node tools/layout/check-layout.mjs`: 891 modules, all checks passed.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.

The source uses default heartbeat and recursion limits. The figures above
record the standalone six-color milestone, before the completed combined
coefficient endpoint and its parent-branch integration.
