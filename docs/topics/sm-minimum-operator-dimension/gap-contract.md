# H2 finite-gap contract

Route A proves C1/C2/H1 exact doubled minima 12/18/18 and H2 an actual
upper bound 20, with lower bound 18. The proposed H2 witness is three signed
down-right fields and three conjugate lepton doublets, plus one dual Higgs:
n=6,h=0,d=1, B3=3,L=-3. Its joint support and original allowance pass.

Before route B, the only remaining grading below 20 is 18: original Lorentz
parity forces n even, the charge lower bound forces n≥6, and the grading
forces n=6,h=d=0. Charge-degree and cyclic neutrality leave two signed charge
possibilities, (B3,L)=(3,-3) and (-3,3). Both signs must be rejected on their
actual inputs; no conjugation transport is assumed.

Use symbolic hypercharge exclusion rather than content enumeration. At each
of the ten species, `abs(Y-B3+6L)≤3`; summing gives
`abs(Y(p)-B3(p)+6L(p))≤3*n` for every pattern. For the two residual charge
possibilities at n=6, Y=0 would require 21≤18. This is an ordinary finite
dictionary inequality and sum/triangle-inequality proof using existing APIs.
The target finite charge-candidate count is two; no occupation, component or
content enumeration is needed or claimed. The reduction and rejection must
be Lean-proved, not inferred from this arithmetic explanation.

The first witness build failed only because the opt-in joint-decision instance
was not locally enabled. It was corrected using the same local-instance
pattern as the existing witness module. The next build passed in 6.8 seconds,
5308972 KiB sampled group peak. No resource cap or proof option was changed.
