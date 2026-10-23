# Whole-grade C4 coefficient theorem

The [public theorem module](../../../Physics/FieldTheory/Jets/HiggsQuarticFourCompleteness.lean)
packages evaluation on q1,q2,q3 as a complex linear equivalence for every
admitted invariant coefficient on the entire free Higgs grade (4,4).
The final gate is recorded in [verification](verification.md); the topic
overview owns its current status.

The input is exactly `HiggsStandardInput.input 0 0`: four independent
field/dual labels, ordinary symmetric four-direction jets, the (+---)
metric, and the actual global covering-SM group times SL(2,C). Selection
takes the preimage of the full unbounded free EOM ideal plus the **linear**
divergence range. It neither truncates relations nor ideal-closes IBP.

The equivalence has an explicit normalized inverse, both inverse laws,
extraction on actual representatives, complex coefficient dimension three,
and direct/generated input agreement. Thus every complex triple is admitted
uniquely within this input. No candidate-span, hypercharge-balance,
semisimplicity, paper count or invariant-extension premise is supplied by
the caller. See the [input guide](input-guide.md).

## Why the whole source is covered

The colored source proof classifies every four-field/order-four monomial,
with arbitrary labels and all 35 derivative allocations. The five sorted
partitions are (0,0,0,4), (0,0,1,3), (0,0,2,2), (0,1,1,2), (1,1,1,1).
Only words with a symmetric derivative pair use the pair-symmetric Lorentz
classification. An explicit linear divergence reduces the all-first-jet
word to the other words; it is never assumed pair symmetric. EOM traces
and contracted IBP identities then reduce the invariant coefficient problem
to metric-pair products.

Actual gauge phase and rotation elements bound all such products by seven
scalar values. Four rotation constraints and the three q values determine
those seven values. Together these facts prove evaluation injectivity on
the entire selected coefficient space. The ordinary linear extension used
to write the calculation factors through the actual full quotient. It is
not asserted invariant outside the grade.

## Constructed lower coefficients

Colored four-wave substitutions kill the full free differential ideal and
every divergence. Three ordered finite node families have 288,72,72 null,
conserving configurations, with scale factors fixed in the source. Their
[complete ordered moments](../higgs-cubature-structure/remaining-results.md)
follow from tensor symmetry and Gram contractions for the transverse and first
collinear families, and wave/node transport for the second collinear family.
Finite kernel checks verify node, phase and Gram identities; wave-slot sorting
retains the old ordered entry routes. No finite-group order or generation
assertion is a theorem premise.

Internal coevaluation expresses the summed color amplitudes as invariant
multilinear pairings. The exact moments express direction dependence as
three Minkowski metric products. Both give invariance under arbitrary
actual group elements on the entire grade. The resulting coefficient values
on (q1,q2,q3) are:

| Family | q1 | q2 | q3 |
| --- | ---: | ---: | ---: |
| Transverse | 12 | 48 | 12 |
| First collinear ordering | 32 | 48 | 16 |
| Second collinear ordering | 16 | 48 | 32 |

The exact inverse matrix constructs three normalized coefficients. The
public theorem discharges all finite moment obligations internally.
Individual old fixed-wave decoders remain quotient separators, without an
invariant-coefficient assertion. The earlier raw polynomial probe still
fails IBP admission.

## Boundaries

The result concerns invariant complex **coefficients**, not the dimension
of the entire un-invariant quotient. It does not establish a global invariant
extension to arbitrary grades, Hermitian real coordinates, local gauge
covariance, nonzero Higgs potential or Yukawa EOM, a full SMEFT basis,
amplitudes or quantum/phenomenological results. The
[literature validation](literature-validation.md) records each native-density
comparison separately, retaining these boundaries.
