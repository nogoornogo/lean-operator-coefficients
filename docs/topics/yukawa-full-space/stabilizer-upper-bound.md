# Finite Stabilizer Upper Bound

Status: bounded endpoint completed and verified. Branch `proof/yukawa-full-space`, integration target
`master`, checkpoint `checkpoint 01`. No merge until the topic endpoint is closed.

## Frozen Endpoint

For every existing full-SU(6) equivariant Yukawa Y, prove that its evaluation
at the unchanged vacuum belongs to `SU6FiveCouplings.massMap H`'s range.
The five-dimensional lower bound is already proved. No new masses, scalars,
vacua, couplings as premises, toolchain changes or external theorem inputs.

The two routes inspected were the full 378-dimensional commutant certificate
and direct restrictions from the vacuum stabilizer. Choose the latter: four
diagonal fourth-root phase rotations and four signed coordinate transpositions
on the first five coordinates, all fixing the sixth. These actual SU(6)
elements must be proved to fix the existing vacuum, not supplied as hypotheses
of the final model theorem.

## Finite Interfaces

1. Transport the existing exterior-square basis and dual coordinate bases to
   the actual 27-dimensional matter carrier.
2. Derive diagonal eigenvalues and the needed transposition actions from the
   actual representation action. Prove the chosen elements fix the vacuum.
3. Prove the finite weight-separation check in Lean. Diagonal invariance kills
   all entries except the ten five/dual pairings and the symmetric singlet block.
4. Transpositions identify the five coefficients within each pairing channel.
   Bilinear extensionality then gives the five-parameter formula and range result.

The finite group need not be the full stabilizer or generate it: invariance
under this subset is enough for an upper bound. The full 22-dimensional
classification and evaluation-kernel dimension 17 are not consequences of
this route alone. Full light-spectrum transport remains a subsequent consumer.

## Verification

- `lake build GUT.SU6.Audit.AuditYukawaVacuumImage`: passed, 4253 jobs,
  43 strict transitive axiom checks. Only propext, Classical.choice and
  Quot.sound; no new axioms or audit exceptions.
- Full `lake build`: passed, 5861 jobs. No new-source warnings; existing
  dependency warnings replayed. Local elaboration errors were corrected
  before these accepted builds; no resource limits or pins were changed.
- `python3 -m unittest discover -s tools/yukawa -p 'test_*.py'`: 8 passed,
  1.1 seconds. The external calculation remains independent supporting
  evidence, not a premise of the new proofs.
- `node tools/layout/check-layout.mjs`: 810 modules, passed.
- `node tools/docs/check-links.mjs`: 305 Markdown files, 1856 links,
  33 fragments, zero errors. `git diff --check`: passed.
- Lean LSP unavailable; used source inspection and targeted builds.
  No new web sources consulted. Qque contraction checks not rerun because
  their covered definitions are unchanged.

## Result

- [VacuumStabilizer](../../../GUT/SU6/Yukawa/VacuumStabilizer.lean): the eight
  actual SU(6) elements fix the original vacuum; every Yukawa evaluation is
  invariant under them. A general coordinate-fixing lemma derives vacuum
  preservation from the existing mass, not from a new hypothesis on Y.
- [StabilizerWeights](../../../GUT/SU6/Yukawa/StabilizerWeights.lean): finite
  ZMod(4) weight separation and the list of allowed pairs, proved with
  kernel-reduced `decide`, not `native_decide` or external certificates.
- [StabilizerBasis](../../../GUT/SU6/Yukawa/StabilizerBasis.lean): a basis of
  the actual analytic matter carrier, its phase eigenvalues and needed swap
  actions; forbidden entries vanish, and the five color/weak entries of each
  of the two pairing channels coincide. `eq_of_entries` determines an
  invariant symmetric bilinear form by two channel entries and its symmetric
  2-by-2 singlet block.
- [VacuumImage](../../../GUT/SU6/Yukawa/VacuumImage.lean): connects those
  entries to the existing probes. `evaluation_mem_range` proves the upper
  bound for arbitrary actual Y; `realized_iff` combines it with the existing
  lower bound. With `massMap_range_finrank`, this classifies the entire
  generated mass space as exactly five-dimensional.
- [Audit](../../../GUT/SU6/Audit/AuditYukawaVacuumImage.lean): persistent
  strict transitive checks; only propext, Classical.choice and Quot.sound
  are accepted.

This does not classify the couplings invisible at this vacuum, prove the
coupling-space dimension 22, or transport the abstract block-kernel theorem
to the actual light representation. The next consumer is that spectrum
transport. The parent topic remains incomplete and unmerged.
