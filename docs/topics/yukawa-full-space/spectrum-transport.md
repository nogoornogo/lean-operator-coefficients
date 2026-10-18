# Spectrum Transport

Status: dimension and singlet endpoints verified; the subsequent
[non-singlet milestone](non-singlet-decomposition.md) closes the residual decomposition.
Branch `proof/yukawa-full-space`, base checkpoint
`checkpoint 01`, integration target `master` (parent topic remains unmerged).

## Frozen Scope

Keep the actual matter, scalar, specified vacuum and neutral residual H.
Construct a bijective coordinate change from UV to the existing 10+5*3+2
block coordinates, prove radical transport, and derive the dimension formula
for all coefficients. Extend by the exhaustive evaluation theorem to all Y.
Then inspect/prove compatibility with the existing SM x H branching and
identify which residual irreducible summands survive in each stratum.

Coordinate relabeling is not a representation decomposition. No equality
of characters alone will be called an equivariant isomorphism. Any remaining
intertwining or irreducibility obligation will be recorded explicitly.
No new group-theory foundations, physical assumptions, numerical premises,
dependency changes or scalar potential are within scope.

## Interfaces

- Actual basis and exact light equations from the preceding milestone.
- Finite bijection of basis labels and linear coordinate transport.
- `SmallSymmetricRank.blockKernelEquiv` / `block_nullity`.
- Existing SU6-to-SM equivariant branching and irreducibility certificates.

## Verification

- `lake build GUT.SU6.Audit.AuditYukawaSpectrumTransport`: passed, 4262 jobs;
  31 strict transitive axiom checks, only propext, Classical.choice and
  Quot.sound. No new-source warnings; existing dependency warnings replayed.
- Full `lake build`: passed, 5866 jobs, rerun after the complement theorem.
- `python3 -m unittest discover -s tools/yukawa -p 'test_*.py'`: 8 passed,
  1.2 seconds. External calculations are supporting controls only.
- `node tools/layout/check-layout.mjs`: passed, 815 modules.
- `node tools/docs/check-links.mjs`: 307 Markdown files, 1867 links,
  33 fragments, zero errors. `git diff --check`: passed.
- Lean LSP unavailable; used source reads and targeted builds. No web sources
  consulted, no pins/resource limits/axioms/audit exceptions changed.
  Qque scripts not rerun: their covered definitions are unchanged.

## Proved Results

[BlockCoordinates](../../../GUT/SU6/Yukawa/BlockCoordinates.lean) constructs
the bijective reordering of all 27 actual basis coordinates. The finite
label bijection is proved by kernel `decide`; no script output is imported.
`coordinate_exterior` and `coordinate_dual` identify its coordinates with
the actual contraction and dual-field coordinates in `LightConditions`.
`radicalBlockEquiv` then transports the ENTIRE radical, not a subspace of
light witnesses, to `SmallSymmetricRank.blockMap`'s kernel.

Let k be 2 minus the rank of the singlet matrix [[u,v],[v,w]]. Then:

| Pairing coefficients | Actual radical dimension |
|---|---:|
| a or b nonzero | 15 + k |
| a=b=0 | 25 + k |

Here k=2 if u=v=w=0, k=1 if the matrix is nonzero with uw-v^2=0,
and k=0 otherwise. `radical_finrank` proves the formula for all coefficients;
`all_yukawa_dimensions` covers every allowed actual Y at this vacuum.
`all_nonzero_dimension_sixteen` checks the fully nonzero rank-drop stratum.

[ResidualSinglets](../../../GUT/SU6/Yukawa/ResidualSinglets.lean) proves the
standard group fixes the actual sixth dual probe and its two-copy singlet
sector. `embedding` and `projection` are actual SM x H intertwiners between
the light radical and the trivial representation on the 2-by-2 matrix kernel.
`singletSplit` proves their composite is identity. `trivialCopiesEquiv` and
`scalar_irreducible` express this factor as k trivial irreducible copies.
The construction works on every rank stratum without choosing numeric masses.
`projection_surjective` and `complement_dimension` also give the invariant
projection-kernel complement dimension: 15 when a or b is nonzero, 25
otherwise. This is not yet its irreducible decomposition.

[Persistent audit](../../../GUT/SU6/Audit/AuditYukawaSpectrumTransport.lean).

## Subsequent Representation Result

The coordinate equivalence used for the dimension theorem is not itself
declared to be an intertwiner. The subsequent
[non-singlet milestone](non-singlet-decomposition.md) constructs a separate
equivariant coordinate map, proves that its constraints are exactly the
existing light equations, and identifies the whole radical with ten plus
one dual-five, or ten plus five plus two dual-fives, and the singlet kernel.
It supplies irreducibility proofs, not dimension-based inference. No new
physical premise is used. The full 22-dimensional coupling classification
remains open; this parent topic stays unmerged.
