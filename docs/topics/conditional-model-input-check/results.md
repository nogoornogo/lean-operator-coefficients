# One-pass candidate results

All ten candidate groups were examined. A restricted input certificate is
separate from its correspondence with the complete literature model. The
[source register](sources.md) freezes versions, variants and locations.

## Summary matrix

| Candidate | Result on the declared coefficient input | New versus reused | Remaining model connection / stopping point |
| --- | --- | --- | --- |
| 1. Constructed parity SM | Full all-degree absolute B1 prohibition, nonzero spectator mass and physical Yukawa coefficients | Re-audit existing simultaneous construction; add B2 six-quark and LLHH consumers | Existing model is algebraic; anomalies and UV origin not certified |
| 2. S3 comparisons | Actual qque forbidden for (perm,trivial,sign), allowed for (perm,sign,sign) and (perm,perm,sign); final dictionary has bijective flavor maps | Re-audit existing selected-sector results | No full physical Yukawa, all-sector classification or UV model |
| 3. DFPW N=1 | Full all-degree B1 prohibition; full uR²dR⁴ content forbidden for every Higgs count under the specified Z18 subgroup | New consumers, beyond earlier four-family/arbitrary-flavor qque certificates | UV/light dictionary and product-cover correspondence supplied; subgroup allowance does not imply full-stabilizer allowance |
| 4. Split SU5 | Gauge-only three-copy input has B1 minimum dimension 6; separately imposed light parity forbids all B1 degrees | New all-degree conditional consumers; old original-mass obstruction retained | Original source uses one generation; three-copy/light maps supplied. Its mixing mass does not automatically preserve light parity |
| 5. Minimal PS | Same gauge-only conditional minimum; optional exact B would forbid B1 | New gauge-only consumer; reuse prior exact-B action obstruction | No extra exact B follows from gauge symmetry; source matching/normalization stop is unchanged |
| 6. Fixed SU6 | Actual qque exterior coefficient survives every supplied ScalarBlockQque.Input | Re-audit existing actual-field theorem | Only fixed scalar/block benchmark; no new mass placements or residual actions |
| 7. Minimal B-L | Before breaking, chosen Z5 subgroup forbids selected six-quark/LLHH contents. After charge-two breaking, declared Z6 input allows B1 at dimension 6, six-quark and LLHH contents | New conditional consumers | Prebreaking subgroup permission is not full U(1) permission. Pure-X charge-six stabilizer/action restriction now proved; UV mass-radical maps and faithful quotient remain external |
| 8. Triplet-breaking LR | Same declared Z6 SM-input result: B1 minimum 6, six-quark/LLHH allowed | Reuse new B-L consumers on a distinct supplied projection | One light-doublet kernel identification now proved under explicit quadratic-coordinate conditions; fermion mass-radical maps and full LR operator classification remain external |
| 9. Ma scotogenic | On SM external fields, exact Z2 is trivial: B1 minimum 6 and LLHH allowed | New SM-even consumer plus exact parity controls | No N/eta external alphabet, loop matching or LFV generation certificate |
| 10. B3/P6 realizations | Single-Higgs charged component restrictions forbid absolute B1/B2 at every mixed degree: new B3 certificate, existing BGW certificate for inverse-generator P6 dictionary | New B3 actual-action proof and finite component dictionary matches | Full MSSM/FN spectrum, multi-Higgs sector and UV-to-light projection not certified; LLHH charge neutrality alone is not an existence proof here |

## New Lean consumers

[ConditionalInputChecks](../../../GUT/Common/ProtonProtection/ConditionalInputChecks.lean)
uses existing actual-space equivalences and certified lower/upper minima.
Dimension statements use twice-dimension grade 12, so mean physical dimension 6.
The negative baryon sign is included by the absolute B1 selector.
The DFPW modulus 18 result follows from the general theorem, not from extending
the old finite 2–12 assignment enumeration by assumption.

For DFPW, q=2,l=0 modulo 18 gives nonzero B1 and selected B2 charge. Its
LLHH space is allowed under this subgroup alone; no inference to the full
stabilizer is made. OriginalForbidden concerns every signed content and Higgs
bidegree in the fixed three-generation derivative-free SM alphabet.

For the B-L comparison X=3(B-L), physical quarks have X=1 and leptons X=-3.
A singlet/triplet charge ±2 corresponds to X=±6. The pure-X cover subgroup
is declared as Z6 with (q,l)=(1,-3); the Higgs is neutral. The source footnote
for the LR example explicitly distinguishes Z6 from its commonly emphasized
Z2 part. A Z5 subgroup of unbroken X has nonneutral six-quark/LLHH charges.
This proves prohibition for the full symmetry *conditional on restriction to
that subgroup*. Conversely its B1 allowance is only a subgroup result; no
subgroup witness is silently promoted to a continuous-group invariant.

[BaryonTrialitySMInput](../../../Physics/StandardModel/Operators/BaryonTrialitySMInput.lean)
constructs actual Z3 copy actions for arbitrary complex multiplicity modules.
The charged Higgs is retained. It adapts the existing BGW scalar-action,
hypercharge and mixed-coefficient proof to modulus three, deriving
9 divides total 3B for every nonzero coefficient. This proves all-degree
absolute B1/B2 vanishing and the corresponding residual-Hom vanishing.
The finite component dictionary matches Eq.(2.17) with n=0,m=p=1.

For P6, invert the generator with n=0,m=5,p=2. The resulting physical field
and Higgs charges match BGW modulo six (`proton_hexality_inverse_dictionary`).
The existing BGW actual-action certificate therefore applies to the declared
normalized component input. This is reuse, not a new MSSM/FN realization.
No neutral-Higgs q/l theorem is applied to B3 or P6.

## Failed routes and exact stops

The full split-SU5 light parity/original-mass admission route remains invalid
for the previously identified parity-odd mixing terms; imposing parity on
light fields is a different conditional input. The PS generated-coefficient
route remains at its recorded normalization and complete UV-transport boundary.
Neither failure prevents the independent gauge-only coefficient checks.

At the initial pass, the LR model check stopped at the single-light-doublet dictionary;
for Ma it stops at the N/eta alphabet and supplied loop/CLFV coefficient map;
for B3/P6 realizations it stops at SUSY/FN spectrum and light-Higgs projection.
The existing selected SM interfaces still supply the restricted results in
the table. No new foundations or model assumptions were silently introduced
in order to turn these missing correspondences into successful model claims.

A first B3 build found adjacent documentation comments after the proof was
adapted; removing the orphaned comment fixed the parser error. No mathematical
route was abandoned and no resource cap was raised.

The candidate pass ends after the [verification](verification.md) gate.
A next pass would require choosing one of the explicit unresolved input bridges;
there is no unfinished proof within the declared restricted endpoints.

## Later B-L / LR bridge continuation

The [continuation result](bl-lr-results.md) closes the pure-X subgroup/VEV/action
restriction and the conditional single-light-Higgs kernel identification. The
initial-pass stopping descriptions above record why that continuation was
needed; the result table reflects the new algebraic bridges. The LR scalar
potential premise and both models' UV fermion-light-spectrum correspondence
remain external. See the [separate verification](bl-lr-verification.md).

## Concrete source-admission status for candidates 7 and 8

The [model-specific recheck](model-admission-results.md) distinguishes the
verified bridge implications from their source premises. Candidate 7's residual
charge/field-action application is checked, while its exact UV light mass
radical remains unverified. Candidate 8's complete one-light-Higgs source
admission is **not verified**: the selected source contract supplies no concrete
potential/parameter point establishing the conditional column-eigenvalue premise.
Formal identity/zero-operator controls show why representation invariance alone
does not establish that premise. The scope of the earlier successful restricted
coefficient results is unchanged.
