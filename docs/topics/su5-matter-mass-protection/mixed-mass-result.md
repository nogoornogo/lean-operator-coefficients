# Additional SU(5) Mass Families: Derived Light Fields And Qque

## Result

[MixedTenMass](../../../GUT/SU5/SelectionRules/MixedTenMass.lean) proves
nonzero physical qque exterior coefficients for independent complex mass
rows on actual `2 ten + bar5 + dual ten` matter. No common UV-copy line or
light membership certificate is assumed. This closes the specified mixed
candidate's actual-field bridge left open at checkpoint `checkpoint 01` and covers
its arbitrary-complex-parameter family.

The common all-left residual character chi on both tens is essential to the
stated class. The bar-five has an independent character psi; the target's
left-handed dual ten carries the dual action. H is ordinary Abelian, with
trivial spinor action. The proofs need no finiteness or topology of H; finite
discrete H is included. They do not classify arbitrary residual/flavor actions.

## Matter, Action And Mass Dictionary

Source: `(Ten × BarFive) × Ten`; all-left fields: source times `Ten*`.
Ten is the actual second exterior power of the SU(5) five. Standard branching
is `(uc, (Q, ec))`. `tenRho` is standard SM action times chi; `barRho` uses
psi. Both original and added tens have the same chi, so every weighted
species map intertwines the genuine SM x H action.

For independent weights a/b with components up, quark, electron, define

```text
M((t, fbar), t') = weighted(a,t) + weighted(b,t')
B(x,y) = y_dual(M x_source) + x_dual(M y_source).
```

The actual branching equivalence defines `weighted`, not an unproved list of
weights. `massMap` is a genuine intertwiner. `ofDirac` derives symmetric
complex-bilinear mass and joint invariance. No full-SU(5) mass invariance,
UV adjoint/scalar coupling or vacuum dynamics is inferred.

`mem_radical_iff` gives the exact radical for every parameter:
`M x_source = 0` and `x_dual` annihilates `range M`. Each species' row is
(alpha,beta). If it is nonzero, use the copy vector (beta,-alpha). If both
entries vanish, use (1,0). The construction proves the selected vector is
nonzero and is in the mass kernel, including all zero/partial rows.

For every species, `quark/up/electronLinear` is injective into the actual
all-left carrier, is in the radical, and intertwines the actual joint action.
The range coordinates identify actual participating fields with standard
charged species. Their characters are all chi, so physical qque is neutral.
`exists_light_exterior` transports the named physical Lorentz/fermionic
coefficient, with right-handed duals for uc/ec, and proves it nonzero.
No unspecified internal tensor is substituted for the physical endpoint.

## Families Checked

| Family | Rows (alpha,beta) for Q / uc / ec | Proved consequence |
| --- | --- | --- |
| Common unmixed | (0,1) / (0,1) / (0,1) | Retained physical coefficient; active-row theorem applies |
| Species-dependent mixing | (1,0) / (0,1) / (1,1) | Nonzero mass, radical dimension 15, physical coefficient on derived mixed fields |
| Partial mass | (0,1) / (0,0) / (0,1) | Nonzero mass, additional added-ten uc zero modes, physical coefficient survives |
| Zero mass | (0,0) on all species | Zero form, radical dimension 35, physical coefficient survives |
| Specified affine splitting | (-1,1) / (4,1) / (-6,1) | All rows active; physical coefficient survives and active-row theorem gives dimension 15 |

The affine subset is defined by `affineRow(m,y) = (m+4y, m-y, m-6y)` in
(uc,Q,ec) order. The labels 4,-1,-6 are sums of the two coordinate labels
from the specified diagonal pattern (2,2,2,-3,-3). This is an explicit
coefficient ansatz. No theorem constructs its UV adjoint Yukawa origin.

For three active rows, `massMap_surjective` constructs a right inverse.
The dual annihilator then vanishes; rank-nullity and the exact radical
identity prove radical dimension 15. `active_mass_nonzero` proves the mass
is nonzero. For partial rows, do not apply the active theorem: the exact
radical criterion and injective species maps remain valid, but the spectrum
can be larger. The specified partial example's dimension 21 is an exact
finite-script result, not a new Lean finrank theorem. No bundled exact full
SM spectrum equivalence is claimed merely from the dimension count.

## What Changed In The Constraints

The earlier fixed-placement condition was sufficient but stronger than needed:
the three light species may use different copy lines. What is retained here
is their joint-action dictionary and neutral residual-character relation.
Their actual light membership is now derived from the mass instead of supplied.

These families do not supply symmetry prohibition. Within the stated class,
changing the six complex mass entries cannot remove the constructed physical
qque coefficient. No generated coefficient, decay amplitude or lifetime follows.
Different residual characters on the two tens, arbitrary flavor actions,
other matter irreps and additional scalar sectors require separate conditions.
The earlier generic compensated-copy C1 interface remains outside this phase.

## Verification And Stop

Focused audit: `lake build GUT.SU5.Audit.AuditMixedTenMass`, 3,897 jobs,
95 strict transitive axiom checks passed; original SU(6) import rejection
passed. Only `propext`, `Classical.choice`, `Quot.sound` are permitted. New
source builds have no warnings; heartbeat/recursion limits and pins unchanged.

Exact controls: the mass script passed six tests and the physical qque script
passed four. The expanded script checks affine rows and partial cancellations
using rational arithmetic; it remains supplementary, not a theorem premise.
Layout check passed 1,269 modules. Full build/link/diff evidence is recorded
in [verification](verification.md).

This additional phase reaches its frozen endpoint for these mass families.
Stop before general residual mixing, complete mass-model enumeration, new UV
coupling sectors or other unification groups. The working branch is retained;
master integration remains unapproved.
