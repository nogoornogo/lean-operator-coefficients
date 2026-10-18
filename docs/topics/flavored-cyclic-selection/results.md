# Results And Verification

## Completed Endpoint

All four dimension-six signed-sector factors and neutral-Higgs LLHH have exact
neutral independent-coordinate equivalences. The full signed exterior input
connects to their product, not a new assumed four-family domain. Both inverses,
cardinality finranks and allowance/prohibition criteria are proved. Empty and
unequal finite multiplicities are retained.

The sources are listed in the [completed dossier](../../proof/current/applications/Physics/FLAVORED_CYCLIC_SELECTION.md).

## Implementation Decisions

The common coordinate theorem needs only `AddCommMonoid`, so the existing
`InvariantFunctionalCoordinates` premise was relaxed from `AddCommGroup`.
Its proofs and existing interfaces are preserved and covered by the full build.

Tensor functionals descend through the symmetric square before neutrality is
tested. This avoids introducing an unnecessary physical dual-carrier dictionary;
signed conjugate charges and their index correspondence are proved separately.
Likewise QQQL reuses the proved finite alternating/mixed/symmetric dictionaries,
whose diagonal-scaling compatibility is proved directly. Thus the weight blocks
in milestone 1 are obtained without implementing unused general exterior-basis
or bidual foundations. This changes no frozen physical input or conclusion.

DUUE keeps the exchange-solved ordered up-pair space, not just its symmetric
branch. QQQL is counted through independent coordinates rather than all neutral
ordered tuples. Its reconstruction proves the sufficiency of those coordinates.

## Controls

- Three trivial-charge generations: full dimension 273.
- All species empty: full dimension 0; empty lepton carrier: LLHH dimension 0.
- Unequal dimensions `(2,1,0,3,1)`, trivial charges: full dimension 21.
- Nonuniform Z2 charges on two Q flavors with one neutral lepton: QQQL dimension
  3, while there are 4 neutral ordered triples.
- General singleton specialization recovers all four scalar family charges and
  the LLHH doubled-lepton charge condition.
- Singleton Z2 quark parity forbids the full four-fermion sector and allows LLHH.

The finite controls use kernel reduction, not native computation or Python.

## Verification

- `lake build Physics.StandardModel.Operators.Audit.AuditFlavoredCyclicSelection`:
  passed, 3,901 jobs and 55 strict transitive checks.
- `lake build`: passed, 6,437 jobs.
- `node tools/layout/check-layout.mjs`: 1,110 modules, no layer, import, cycle,
  aggregate or relocation errors.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.
- `node --test tools/docs/test-check-links.mjs tools/layout/test-check-layout.mjs`:
  14/14 passed. The first sandboxed run could not create the temporary Git test
  fixture; the same command passed with the required filesystem permission.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed transitively by
the persistent new audit. No new warning remains in the new sources. The full
build retains the repository's existing audit informational output.

## Integration And Boundaries

Working branch: `proof/flavored-cyclic-selection`; target: `master`.
Proof checkpoint: `checkpoint 01`. The user explicitly authorized master integration.
Git ancestry records the integration commit; merged-state verification repeats
the full build, strict audit, layout and local-link checks. The historical topic
branch name is retained here after safe local branch deletion.

No AutoEFT installation, anomaly/Yukawa compatibility, physical rate, UV matching,
general nonabelian executable Hom classification or general six-quark flavor
selection is included. No external literature theorem is added as a premise.
