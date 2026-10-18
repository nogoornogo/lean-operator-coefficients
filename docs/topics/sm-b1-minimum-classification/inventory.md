# Pre-gap inventory and single-pass witness proposals

The retained diagnostic `tools/structural-support/b1-minimum-inventory.py`
reads the 18 existing B1 witness grades and three new small witnesses. It
reconstructs the existing natural-representative domain, without CSV input.
Its initial proposed normalized-charge lower grade is
`max (3*(3+abs(L))) ((3+abs(L))+2*abs(2*L-1))`, from charge-degree and the
existing hypercharge envelope. This lower bound still needs a Lean proof.

The initial diagnostic has 326 allowed rows, 160 matching intervals and
166 gaps. Maximum doubled upper bound is 70; maximum doubled gap is 16.
The proposed initial (lower,upper,count) groups are:

| Doubled lower | Doubled upper | Rows |
| ---: | ---: | ---: |
| 12 | 14 | 48 |
| 18 | 18 | 98 |
| 20 | 20 | 62 |
| 26 | 36 | 28 |
| 30 | 38 | 16 |
| 36 | 46 | 16 |
| 40 | 56 | 10 |
| 46 | 60 | 28 |
| 50 | 62 | 10 |
| 56 | 70 | 10 |

These are diagnostic proposals, not imported theorem premises or exact
minima. The first script draft had a Python parenthesis SyntaxError, corrected
before producing this inventory. No Lean/resource failure is associated with it.

## Route B: frozen proposed replacement templates

The 326 rows need minimum absolute L at most eleven. Try the following eight
new templates once each, using balanced generation occupations and the first
live branch of the existing exact joint presentation. The six other extreme
signed charges retain existing families; no row requires a smaller charge
outside this inspected range. Each proposed support result must be kernel
checked; failure preserves the existing upper bound and is not prohibition.

| L | Counts by named signed species | (h,d) | Doubled grade |
| ---: | --- | --- | ---: |
| 5 | uR³ L⁴ eR | (2,0) | 28 |
| -5 | dR³ conjugate(L)⁵ | (0,3) | 30 |
| 7 | uR³ L⁶ eR | (4,0) | 38 |
| -7 | dR³ conjugate(L)⁷ | (0,5) | 40 |
| 9 | uR⁴ conjugate(dR) L⁹ | (3,0) | 48 |
| -9 | dR⁵ conjugate(uR)² conjugate(L)⁹ | (0,3) | 54 |
| 11 | uR⁶ conjugate(dR)³ L¹¹ | (1,0) | 62 |
| -11 | dR⁷ conjugate(uR)⁴ conjugate(L)¹¹ | (0,1) | 68 |

No repeated branch/occupation search or exhaustive content enumeration is
authorized by this pass. Exact lower bounds may still fail to meet these
improved upper bounds. In that event the plan stops with verified intervals
and the exact unresolved row set, rather than claiming complete exclusion.

Before testing, chirality inspection corrected the +9/+11 proposals in the
initial draft: an odd number of quark/antiquark pairs requires no eR factor,
with one additional L and one fewer Higgs. The corrected explicit source
was materialized before its single kernel run. All eight corrected proposed
supports pass together in 7.3 s at 5242324 KiB. No second occupation/branch
search was used.

Source inspection also found the existing complementary mixed weak-capacity
bound. It permits a symbolic bound `abs(7*L-B3)≤12+twiceDimension`, without
enumerating contents. Combined with independent-chirality engineering-grade
parity, this may close the remaining gaps; it is not a new representation
foundation or an assumed multiplicity statement.
