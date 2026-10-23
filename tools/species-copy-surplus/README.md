# Species Copy Surplus Exact Controls

Run `python3 tools/species-copy-surplus/audit_controls.py` from the repository
root. Six deterministic unittest cases use standard-library exact fractions:
unequal species counts and independent kernels; all 729 2×3 matrices over
{-1,0,1}; nontrivial C2 copy weights; disjoint constituents despite positive
total dimensions; permission without shared-R surplus; neutral Majorana blocks
and a source/rest mixing negative control.

The matrix enumeration is exhaustive only over that finite integer domain,
not arbitrary complex masses. These computations are not theorem premises,
Lean oracles, UV parameter witnesses or model branching proofs. They supplement
[the proved general bridge](../../Physics/FieldTheory/Mass/Surplus/PhysicalSpeciesCopySurplus.lean).
Rerun them when the corresponding mass/block/charge conventions change.
