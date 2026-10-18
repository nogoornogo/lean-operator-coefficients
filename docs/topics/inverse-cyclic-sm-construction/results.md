# Bounded Inverse Construction Result

## Endpoint

The first planned algebraic construction succeeds. Enumerating Yukawa-neutral
universal cyclic charges for orders 2 through 12 leaves 572 of 649 labeled
pairs after the necessary BNV test. The lexicographically first survivor is
k=2, q_Q=0, q_L=1. It is the familiar lepton-parity assignment, not a newly
discovered physical protection model.

The actual three-generation field action, a nonzero invariant spectator mass
with precisely those SM fields as its radical, nonzero charged-fermion Yukawa
exterior coefficients and derivative-free all-degree B1 prohibition are
proved on the same constructed input. The simultaneous theorem is
`InverseCyclicSMYukawa.construction_certificate`.

This endpoint is algebraic. Anomaly freedom, an exact quantum symmetry, an
origin for Z2 and a simple-group UV lift are not established. In particular,
this is not a certified realistic stable-proton model. Those are separate
scope decisions, not silently assumed properties of the construction.

## Finite charge computation

`InverseCyclicSMCharges.yukawa_parametrization` proves that the all-left
neutral-Higgs Yukawa constraints give

    (q_Q,q_uc,q_dc,q_L,q_ec) = (q,-q,-q,l,-l).

In the signed physical convention the positive-species charges are
(q,q,q,l,l), with conjugate species carrying the opposite. All four bounded
BNV family charges equal 3q+l. The one-generation bounded sector has an exact
forbidden iff, and `three_generation_necessary` applies the actual flavored
coefficient classification: if 3q+l=0, a concrete DUQL coordinate exists.
Thus a prohibition covering that bounded participating domain cannot hold.
The subsequent [bounded converse](bounded-converse-results.md) makes the
three-generation bounded test an iff. It does not upgrade it to an all-degree iff.

| k | Yukawa-parametrized pairs k^2 | Retained k(k-1) |
| --- | --- | --- |
| 2 | 4 | 2 |
| 3 | 9 | 6 |
| 4 | 16 | 12 |
| 5 | 25 | 20 |
| 6 | 36 | 30 |
| 7 | 49 | 42 |
| 8 | 64 | 56 |
| 9 | 81 | 72 |
| 10 | 100 | 90 |
| 11 | 121 | 110 |
| 12 | 144 | 132 |
| Total | 649 | 572 |

Lean kernel reduction verifies these finite cardinalities. No external script
or native decision oracle supplies a proof premise. Equivalent or nonfaithful
assignments are not removed. The numbers count labeled charge pairs, not
independent physical models. Orders outside the declared interval are not
classified. The selected assignment precedes all others in the declared order;
its all-degree certificate is proved independently, so no earlier arithmetic
survivor is skipped.

## Actual field and mass construction

The five all-left species use signed-alphabet positions (0,6,7,3,9). Each has
three flavor coordinates. `threeCopies` gives an actual equivariant
identification with three copies of its standard gauge representation.
`gauge_restriction` proves forgetting Z2 leaves that SM action.
`selected_dictionary` verifies the selected charge tuple, and
`physicalFieldEquiv` proves the gauge/flavor/spin regrouping into the existing
coefficient alphabet. `flavorDualEquiv` explicitly identifies opposite flavor
actions with the algebraic dual. The Higgs and its conjugate are neutral.

The original fermion carrier is light SM fields plus a charged gauge-singlet
spectator and its algebraic dual. Its symmetric mass is zero on the SM block
and evaluation on the spectator pair:

    B((v,w,phi),(v',w',phi')) = phi'(w) + phi(w').

`ConstructedSpectatorRadical.radicalEquiv` proves the radical is exactly the
specified light representation. This is a constructed mass, not an assumed
radical dictionary or UV-index target. `spectator_mass_nonzero` verifies that
the original mass is not identically zero. No scalar potential or splitting
mechanism is inferred from this deliberately chosen block mass.

## Yukawa and prohibition proofs

Gauge contractions use weak epsilon for Q uc H and evaluation for
Q dc H-dagger and L ec H-dagger, retaining their hypercharges. Explicit basis
values prove nonzero. The generation covectors, residual characters and left
Weyl epsilon are combined before distinct-species exterior descent. The three
nonzero statements refer to the actual selected light species and the one-
Higgs carrier. They certify existence in each Yukawa channel, not a realistic
full-rank flavor matrix or observed masses/mixing.

For any coefficient on the signed SM/Higgs alphabet, Lorentz invariance
forces an even number n of fermions. For every signed species,

    3B + L = 1 mod 2.

Summing gives total 3B+L = n mod 2. Residual lepton parity forces total L even
on a nonzero coefficient. Therefore total 3B is even and cannot have absolute
value 3. This proves all-degree absolute B1 prohibition; no degree cutoff or
four-family extrapolation is used. The result is also transported to the
selected residual-Hom product via the existing decomposition interface.

## Difference from the previous filter

The prior topic proved necessary conditions conditional on actual action and
mass-radical dictionaries. This topic derives finite charge candidates and
then constructs one such dictionary, its mass and actual coefficient
certificates. It closes a bounded existence endpoint for an extended-SM
algebraic input. It does not solve inverse construction for simple GUTs or
prove that every filter survivor can be realized or protected.

The planned stopping point is reached. See [reader study](../../model-studies/inverse-cyclic-sm/README.md),
[proof dossier](../../proof/current/applications/Physics/INVERSE_CYCLIC_SM_CONSTRUCTION.md),
and [verification](verification.md). Any anomaly/UV-completion investigation
requires a new frozen scope; no master merge or push is implied.

## Milestone: bounded converses and assignment properties

The [three-generation bounded converse](bounded-converse-results.md) proves
prohibition iff 3q+l != 0 for the actual oriented dimension-six sector. The
[three follow-ups](three-followups-results.md) add the restricted diagonal
LFV converse, exact one-copy B2/LLHH adapters and fixed-order unit equivalence.
The 572 labeled assignments form 151 generator orbits; 316 forbid both
additional specified one-copy domains.

This is a completed milestone converting selected sufficient conditions into
exact criteria at explicit scopes. It does not make every sufficient condition
necessary, classify all-degree B1 protection or realize all surviving UV models.
The user authorized integration into master at stage 01. Further converse
work belongs to a new topic branch with its own frozen contracts.
