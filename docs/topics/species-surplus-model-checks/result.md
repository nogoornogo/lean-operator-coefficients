# Three Model Recheck Result

The bounded pass is closed. The new theorem removes the *common full source
and target* restriction: the required common object is now one irreducible R
with positive species-wise Hom surplus. It does not remove the requirement for
that common constituent, actual action or invariant original mass.

| Supplied dictionary/action | Q,uc,ec surplus | Decision |
| --- | --- | --- |
| B/L, surviving Z18 subgroup | Supports Q={2}, uc={16}; no shared R | Inlet obstructed, even with all charged exotic copies |
| Split SU(5), H=1 | R=trivial: (1,1,1), from (3→2,3→2,1→0) | Direct inlet admission on full supplied SM sectors, for arbitrary invariant symmetric mass |
| Split SU(5), selected light parity | Q,uc even; ec odd | No common R on these selected ranges |
| Split SU(5), full Eq.(22) parity imposed exactly | R=odd: (1,1,1) | Inlet admitted, but original parity-odd mixing masses excluded; different mass model/light placement |
| Minimal PS, H=1 | R=trivial: (1,1,1), from (1→0) in each species | Direct inlet admission; neutral Majorana masses unrestricted |
| Minimal PS, optional exact U1_B | All-left weights (1,-1,0) in units 3B | No shared R; higher operators need not obey this optional action |

## What Is Now Closed

For H=1, Hom from the trivial complex line to an n-copy trivial representation
has dimension n: its intertwiner is determined freely by the image of 1. The
sources are semisimple and R is irreducible. Thus the numeric differences above
are the actual Hom surplus of the theorem, not merely a total gauge dimension
count. The copy targets include *all* opposite gauge species from the supplied
branching; the rest is what remains after removing those entire sectors.

In both admitted dictionaries Q/uc/ec have nonzero hypercharge, excluding
same-species mass pairing. All matching opposite gauge representations are
already in the selected partner sector; inequivalent remaining irreducibles
cannot pair with the source. Gauge irreducibility then supplies factorization.
Consequently the [generic constructor](../../../Physics/FieldTheory/Mass/SpeciesSectorPresentation.lean)
derives mass maps/squares for every original SM-invariant symmetric B on this
supplied carrier. The [physical theorem](../../../Physics/FieldTheory/Mass/PhysicalSpeciesCopySurplus.lean)
produces actual radical ranges and nonzero physical qque on them. No independently
selected light line is used as an admission premise.

The split kernel directions may differ. Neither rank-two assumptions nor pure
40/50 light-origin determinant conditions are needed for this permission result.
Such conditions belong to the more specific UV light-placement question.
Independent sources directly handle unequal e versus Q/u copy counts, removing
the earlier common-copy *feasibility* step on this supplied SM dictionary.

For the obstructed actions the scalar supports already differ. Any nonzero
intertwiner from an irreducible R into a scalar source forces that scalar action
on R (a nonzero map is injective). Distinct Q/uc weights for B/L or accidental B,
or even Q/uc versus odd ec for light parity, prevent a shared R. For B/L it
suffices to restrict a proposed full-residual R to the surviving element: the
scalar conflict remains, even if its restriction is reducible.

## Evidence Level And Stop

[The model notes](../../model-studies/README.md) link the three individual
rechecks. The [exact script](../../../tools/species-surplus-model-checks/README.md)
checks supplied labels, copy differences, charge supports, full/light parity,
rectangular masses and neutral masses. These are supplemental finite diagnostics,
not a new Lean proof of literature branching, multiplicities or NoPairings.
The general implication is Lean-proved on the parent branch; the dictionary
admission arguments here are documented conditional algebraic applications.
No new full-model Lean adapter or UV parameter witness is claimed.

The finite stop is reached: all three models/actions have an explicit admission
or obstruction and an original-mass compatibility check. Full UV decompositions,
residual/global descent and representation adapters remain external inputs.
Generation, matching, proton-decay rates and all-loop/nonlinear claims remain
outside this pass. No counterexample to the parent theorem is found.
