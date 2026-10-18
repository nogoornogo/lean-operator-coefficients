# Z5 Pattern-Search Validation

The [new bounded family](pattern-search-plan.md) uses catalogue G4 and the
mixed prohibition/allowance pattern. It is different from the previous Z4
matrix candidates and the original scalar/block obstruction.

## Search and formal output

Solve the ordinary all-left Yukawa charge equations with
`Q=x, L=y, H=h, U=-x-h, D=-x+h, E=-y+h` in ZMod 5.
The selected residual charges are

```
qque: 2Q-U-E = 3x+y
LLHH: 2(L+H) = 2(y+h).
```

The [finite search](../../../tools/su6-light-placement-search/check_z5_patterns.py)
checks all 125 triples. Twenty have nonzero qque charge and zero LLHH
charge: four with neutral Higgs and sixteen with charged Higgs. The numbers
are exact script results, not a Lean enumeration theorem. A concrete witness
is `(Q,U,D,L,E,H)=(1,4,4,0,0,0)`. The neutral assignment is a negative control.

[The Lean consumer](../../../GUT/SU6/SelectionRules/Models/CyclicPatternSearch.lean)
proves the charge simplification and witness, then actually applies
`Math.ProhibitionPatterns.cyclic_forbidden_iff` and `cyclic_neutral_allowed`.
`mixed_iff` states that, for supplied genuine representations on nontrivial
carriers with the specified scalar actions, qque-carrier prohibition and
LLHH-carrier allowance are equivalent to these two charge tests.
`package` places proved prohibition/allowance in the mixed request interface.
`character_line_iff` and `character_line_witness` instantiate the consumer
on actual one-dimensional cyclic representations, so the pattern has a checked
inhabitant and is not only an uninstantiated conditional implication.

## What was gained

A user request fixes the desired forbid/allow outputs; the charge-family
parameterization fixes the search inputs. The pattern converts those inputs
into an iff, and finite enumeration finds all matching parameter assignments
within this family. One adapter serves every triple, rather than writing
twenty independent model certificates. The character-line instance validates
the pattern machinery without claiming that a line is a physical operator
quotient.

The script additionally checks equality of the four familiar dimension-six
BNV charge expressions under these Yukawa conditions. This is charge
arithmetic, not a proof of all-degree B1 prohibition or physical completeness.
Yukawa charge neutrality permits interactions by the residual symmetry;
it does not prove actual invariant contractions or generated nonzero couplings.

## SU(6) admission boundary

Every matching charge assignment violates the neutral qque relation in the
prior fixed scalar/block light placement. It therefore supplies a useful
filter: an SU(6) realization must change that placement/action class rather
than claim to instantiate it unchanged. No new UV-covariant SU(6) action,
anomaly cancellation, scalar/VEV mass realization or actual-light dictionary
is supplied by this search. Arbitrary charged-Higgs carrier admission is
likewise not automatic.

The formal character lines are not the physical qque/LLHH spaces. Application
to actual fields requires their nontrivial local quotient and scalar-action
transport, exactly as `mixed_iff` states. Thus twenty matches are twenty
charge-level candidates, not twenty protecting models. The authorized
pattern-search validation stops here with its explicit UV-input obligations.
