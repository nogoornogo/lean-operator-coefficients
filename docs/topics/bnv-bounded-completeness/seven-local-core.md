# Dimension-Seven Local Cores And Degree Transport

## Verified Local Dictionaries

[BnvSevenLocal](../../../Physics/StandardModel/Operators/BnvSevenLocal.lean)
proves complete reduced dictionaries using independent color, weak and full
Weyl actions. The color epsilon is the unique three-color invariant. The
two-weak-doublet epsilon is unique; four weak doublets have two independent
pairings. Four same-chirality Weyl slots have two pairings, whereas the
two-left/two-right contraction is unique.

Combining these proved statements gives the three local cores needed by the
four dimension-seven patterns: two weak slots with four right slots (rank 2),
four weak slots with two-left/two-right slots (rank 2), and two weak slots with
two-left/two-right slots (rank 1). The first core is reused by two patterns.
Explicit normalized probes and reconstruction determine these ranks. The
`sameFlavorEquiv`, `mixedFlavorEquiv`, and `mixedFourWeakFlavorEquiv` turn each
core into residual Hom coordinates for representations of arbitrary abstract
residual groups, without topological or continuity assumptions.
The two multi-coordinate consumers also descend through supplied local/flavor
exchange maps to an explicit relation-quotient Hom.

These are **reduced-core results**, not yet full typed physical-family results.
The charged gauge and species/spin regroupings must be constructed, and the
actual repeated-field exchanges must be connected to the input exterior power.
No such transport is hidden as a completeness premise.

## Input And Dual Transports

[WeakContragredient](../../../Physics/StandardModel/Gauge/WeakContragredient.lean)
now supplies `chargedWeakDualEquiv y` for every integral charge. It identifies
the charge-y weak doublet with the algebraic dual of the charge-minus-y doublet;
it does not erase hypercharge. The inverse has the explicit two-epsilon-probe
formula. This reuses the existing epsilon-dual identification.

[SymmetricPowerLowDegree](../../../Math/LinearAlgebra/SymmetricPowerLowDegree.lean)
constructs degree-zero/one symmetric-power equivalences with explicit inverses
and equivariance. `MixedWeightSupport.zeroBosonEquiv` and `oneBosonEquiv` apply
them to the independent exterior/symmetric input, without basis choices.

[BnvSevenDegreeDecomposition](../../../Physics/StandardModel/Operators/BnvSevenDegreeDecomposition.lean)
proves that the complete independent bounded input through seven is linearly
equivalent to its degree `(4,0)` and `(4,1)` BNV coefficient factors. Every other
degree is proved zero; reconstruction uses two dependent single insertions.
This is a two-sided **degree decomposition**, not the final family/Hom product.

## Remaining Connections

The single-boson typed descent is now two-sided.
`MixedSingleBosonDescent.equiv` descends an alternating fermion map with a
linear spectator through the exterior/symmetric carrier. For any slot count,
`MixedSinglePatternAssembly.equiv` identifies one orbit-supported coefficient
space with ordered maps satisfying actual group invariance and identical-field
exchange compatibility. Its inverse uses normalized alternatization, with
canonical extraction, off-orbit vanishing and injectivity proved internally.
There is no spanning premise or finite-dimensional multiplicity assumption.
`BnvSevenPatternDescent.equiv` applies it to the four positive dimension-seven
patterns on actual signed SM carriers. Their baryon and hypercharge values
are checked, and `family_bnv` proves inclusion in the independent BNV sector.
This does not yet identify these ordered spaces with the reduced-core Homs or
identify the local residual Homs. The simultaneous signed-family split is now
proved in [the separate checkpoint](seven-family-split.md).

1. Construct the four charged typed family regroupings and their conjugates.
2. Descend each ordered family through its actual fermion exchanges, and split
   the mixed input by the internally derived species support.
3. Connect the signed BNV zero-boson degree to the existing positive and
   conjugate dimension-six family endpoints. The input transport itself is
   proved by `BnvZeroBosonBridge.equiv`: it identifies the independent mixed
   degree `(4,0)` with the signed exterior BNV input and preserves typed pure
   extraction. `lepton_support` derives lepton degree plus/minus one without
   an initial lepton-degree assumption.
4. Assemble the entire seven-dimensional residual product and prohibition iff;
   only then proceed to the higher-dimensional local dictionaries.

The topic is still in progress. These local cores do not complete the seven
or eleven-dimensional acceptance gate.

## Verification

- `lake build Physics.StandardModel.Operators.Audit.AuditBnvBoundedSupport`:
  passes, 94 strict transitive checks; only the standard logical axioms are
  accepted and model-layer imports are rejected.
- `lake build`: passes, 6,463 jobs, no residual warning introduced here.
- `node tools/layout/check-layout.mjs`: passes, 1,136 modules.
- `node tools/docs/check-links.mjs` and `git diff --check`: pass.

The charged-dual, low-degree symmetric-power, reduced local dictionaries,
degree decomposition and scalar-free signed-input bridge are included in
the persisted strict audit.
