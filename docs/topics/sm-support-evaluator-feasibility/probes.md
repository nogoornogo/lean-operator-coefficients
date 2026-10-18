# Frozen probe manifest

This manifest is frozen before Lean measurements. Later stages are conditional
on the earlier gates; an unrun probe is not evidence for or against its result.
Species indices: Q=0, U=1, D=2, L=3, E=4; conjugates add five.
Original-space probes use k=1 and q=l=0, so residual charge is neutral.

## Local gates

- SU2 leaf 0: true; leaf 1: false; tensor(1,1): true;
  tensor(1,2): false. These follow from the CG degree formula.
- Color unit symmetric(0): true; symmetric(1): false by triality;
  symmetric(1) tensor oppositeSymmetric(1): true by evaluation;
  three distinct symmetric(1) leaves: true by determinant.
  A single symmetric(3) leaf is false (repeated triple owner);
  a single adjoint leaf is false (internal pair).
  Reverse and dual versions retain the corresponding outcomes.
- Expression zero: false, including overflow core degrees.
- Metadata access: Q core degree 0 and 6 and their conjugates;
  occupation enumeration at total 0 and 2. No support claim is inferred merely
  from successfully reading a branch expression or counting occupations.

## At most twelve original-space probes

Counts not displayed are zero. All h,d are natural numbers.

| ID | content | h,d | expected | reason/reference |
| --- | --- | --- | --- | --- |
| LLHH | L^2 | 2,0 | true | existing LLHH witness |
| conjugate-LLHH | conjugate L^2 | 0,2 | true | conjugate witness |
| weak-bound-zero | E^2 | 4,0 | false | Y=-12 cancels 3(h-d), but no weak slots and h differs from d |
| DUQL | D U Q L | 0,0 | true | existing sector witness |
| QQUE | Q^2 U E | 0,0 | true | existing sector witness |
| QQQL | Q^3 L | 0,0 | true | existing sector witness |
| DUUE | D U^2 E | 0,0 | true | existing sector witness |
| mixed-conjugate | Q conjugate Q | 0,0 | false | independent left/right spin factors cannot be singlets |
| Q6 | Q^6 | 0,2 | true | local m=2,delta=-2 reference multiplicity 261 |
| Q18 | Q^18 | 0,6 | true | local m=6,delta=-6 reference positive |


The neutral-zero stress control is **local**, not an original-space assertion:
Q^24, m=14, delta=-8, multiplicity zero in the external diagnostic. Choosing
an original bidegree could admit other weak constituents and change support.
The ten original-space controls above and this one local stress key are fixed.
Sector expectations are validation targets until the corresponding source
witnesses are checked; no literal positive/conjugate field convention is assumed
without that check. The first local/metadata gate does not execute these rows.

## Deferred diagnostic domain

The 107-row comparison is exactly the distinct (species,fermions,m,delta) keys
of `tools/exact-rank/neutral-sparse-results.csv`. Compare local support with
multiplicity > 0, not numerical rank or original-space support at an arbitrary
bidegree. The data are external controls, never proof premises.
