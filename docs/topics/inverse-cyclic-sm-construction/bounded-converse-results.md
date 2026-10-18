# Three-Generation Bounded Cyclic Criterion

## Exact result

For every positive cyclic order k and universal physical charges
(Q,uR,dR,L,eR)=(q,q,q,l,l), the actual three-generation derivative-free
dimension-six DeltaL=1 four-fermion sector satisfies

    prohibition <-> 3q+l != 0 mod k,
    nonzero coefficient exists <-> 3q+l = 0 mod k.

The all-left charges are (q,-q,-q,l,-l), retaining the neutral-Higgs Yukawa
parametrization. No new semisimplicity, mass, UV-lift or nonzero-coefficient
premise is introduced. The theorem fixes the same three generation indices
and actual cyclic flavor representations as the preceding necessary lemma.

The sector is `DeltaLOneSignedFields.Sector ... 1`, with its existing DUQL,
QQUE, QQQL and DUUE classification. The orientation and degree remain fixed.
This is not an iff for every all-degree absolute B1 content, other light
alphabets or quantum protection. The order range 2 through 12 belongs to the
finite enumeration only; the symbolic iff covers every positive k.

## Proof and declarations

[InverseCyclicSMCharges](../../../Physics/StandardModel/Operators/InverseCyclicSMCharges.lean)
adds:

- `universal_qque_charge`: every symmetric quark-pair coordinate, including
  repeated flavors, has total charge 3q+l.
- `universal_qqql_charge`: symmetric, alternating and mixed Young coordinates
  all carry that same charge. No redundant ordered triples replace the basis.
- `three_generation_sufficient`: nonzero common charge makes all four typed
  neutral-coordinate index sets empty.
- `three_generation_forbidden_iff`: combines that proof with the existing
  necessary direction, which constructs a DUQL coordinate when charge is zero.
- `three_generation_allowed_iff`: the actual coefficient allowance converse.
- `candidate_iff_three_generation_forbidden` and
  `not_candidate_iff_three_generation_allowed`: connect the finite arithmetic
  filter and its complement to these actual bounded coefficient predicates.

The proof uses the existing full flavored coordinate equivalence; it does
not assume a neutral raw tensor survives statistics. In the neutral case,
the DUQL coordinate already belongs to the proved actual coefficient dictionary.

## What the finite table now means

The previous 649 labeled Yukawa-parametrized charge pairs and 572 survivors
are unchanged. For this bounded three-generation sector, exactly those 572
assignments prohibit every coefficient; the other 77 assignments admit a
nonzero coefficient. These are assignments on constructed flavor actions,
not 649 or 572 realized UV models.

For the stronger all-degree request, the 572 entries remain candidates only.
The independently constructed Z2 lepton-parity input still has its separate
all-degree certificate. This converse adds no all-degree realization or
classification for the other assignments.

## Scope and verification

The O7 contract is complete. The restricted diagonal-cyclic LFV converse,
one-copy B2/LLHH adapters and fixed-order unit-orbit tables are also complete;
see the [bounded follow-ups](three-followups-results.md). General LFV,
whole-exterior and all-degree converses retain the separate boundaries in
the [inventory](converse-inventory.md). No new model, anomaly, rate, dependency or
foundational project is introduced. The [verification record](verification.md)
contains focused strict audits, full build and document checks.
