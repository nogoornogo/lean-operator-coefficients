# Unverified Leanstral topology drafts

Archived at stage 01 from commit `checkpoint 01` on `mistral-vibe`.
These `.lean.txt` files are historical review material, not Lean modules,
accepted mathematical assumptions, or part of any build. Apart from an archive
header, the submitted drafts are preserved. Git retains their original paths.

The user stopped local/cloud prover delegation and approved a literature-input
boundary instead. See [the replacement](../../../proof/current/inputs/GUT/E6_LITERATURE_BOUNDARY.md).

This archive was relocated from `notes/archive/e6-leanstral/` at stage 01.
The six `.lean.txt` drafts are unchanged by that move. The archived
[status report](E6_status.md) retains its rejected claims for review, not as
current conclusions. Do not resume work from these drafts; use the
[current E6 topic](../README.md).

## Rejected Claims

- Fixed-T centralizer locus is not the global regular locus. Including the
  whole torus forces G = T by testing the identity.
- Neither equality nor containment of nearby centralizers in a fixed T
  follows from sequential closedness of commuting pairs.
- The relative-avoidance draft does not provide the required boundary-fixed
  homotopy; its embedding variable is also scoped incorrectly.
- The conjugation-map draft does not compile. A product open set need not be
  a single rectangle; a positive-dimensional torus quotient is not a covering.
- The torus has fundamental group Z^6, not zero. Its loops contract in the
  candidate, not in the torus.
- L7/L8 declarations ended in unproved placeholders, not compositions of
  earlier results. Allowing their placeholder axiom is not a proof audit.
- The root-space draft contains no group/Lie centralizer bridge. Its earlier
  nonvanishing-at-one condition was wrong; changing it to zero did not prove it.

## Preserved Work

Path connectedness, smooth torus inclusion, all-root regular-point construction,
and the valid singular-locus inclusions remain in `GUT` and are built by the new
audit. The checked sequential centralizer lemma and fixed-centralizer definition
projections remain in cleaned original modules. The valid `CoveringBundle`
wrappers remain, without claiming applicability to the torus quotient bundle.
No previous kernel-checked E6 construction or physical theorem is discarded.
