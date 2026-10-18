# SU(6) Four-Direction Screen

Run from the repository root with standard-library Python only:

```sh
python3 tools/su6-light-placement-search/check_four_directions.py
python3 tools/su6-twisted-protection/audit_block_phase.py
python3 tools/qque/audit_one_generation.py
```

Four tests cover six coordinate mass/VEV directions, hypercharge-allowed
symmetric entries on the 27-field carrier, 512 selected Z4 enlarged-placement
cases plus one rank-42 57-field representative, and an independent fifteen
phase candidate. Integer phases/weights and Fraction rank are exact.
The matrix-unit and qque-polynomial implementations are reused from the prior
bounded audits; their controls are rerun. No sampling or new dependency.

The counts and scope are documented in
[results](../../docs/topics/su6-light-placement-search/four-direction-results.md).
These are not Lean proofs, full-group certificates or premises for formal
prohibition theorems. Rerun these checks when their fields, phases, matrices,
contractions or implementation dependencies change.

## New Z5 pattern-search check

`python3 tools/su6-light-placement-search/check_z5_patterns.py` exhausts 125
Yukawa-compatible charge triples and checks the selected qque-forbidden /
LLHH-neutral condition plus positive/negative controls. It finds twenty
charge assignments. Counts are computational; the G4 iff and one witness
are separately Lean-proved. No physical carrier, UV model or anomalies are
certified by this script. See [results](../../docs/topics/su6-light-placement-search/pattern-search-results.md).

`python3 tools/su6-light-placement-search/check_z5_orbits.py` reruns the Z5
census, verifies five four-element generator orbits and unique qque-charge-one
representatives, and screens all representatives against 125 determinant-
compatible scalar/block phase inputs. A separate hypercharge-dressing check
connects the five representatives only at charge level. Six generic algebraic
lemmas are separately audited in Lean; census counts are computational.
See [orbit results](../../docs/topics/su6-light-placement-search/orbit-screen-results.md).

`python3 tools/su6-light-placement-search/check_small_branching.py` constructs
complete characters of 1,6,15,20,21,35,70 and conjugates, subtracts/reconstructs
full SM irreducible characters, and checks an exact charge-resolved index
system for all five normalized Z5 targets. The neutral spectrum is a positive
index control. Fraction Gaussian elimination is a computational necessary
condition test, not a Lean branching/mass certificate. See
[reverse-placement results](../../docs/topics/su6-light-placement-search/reverse-placement-results.md).

`PYTHONDONTWRITEBYTECODE=1 python3 tools/su6-light-placement-search/check_lean_index_data.py`
checks the static finite Lean tables against the complete-character computation
and target charges. It additionally checks the 175 annihilation and five
separation identities. The actual finite identities and no-solution theorem
are kernel-checked in Lean; this script is not their premise. Actual continuous
branching and mass-index admission remain separately required.
