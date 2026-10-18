# 40/50 Copy Bounds: Formal Certificate and Physical Connection Gate

The [bounded plan](new-family-plan.md) reaches a formal-index certificate and
an actual-connection feasibility stop. No new physical no-go is claimed.
The selected 40/50 dictionary was previously studied conditionally; extending
it to variable copies is new to this continuation, not a new literature model.

This is the original formal-feasibility checkpoint. The subsequent
[full actual family result](full-family-results.md) proves the relevant
hypercharge-index rows from actual representations and arbitrary masses,
without using the supplied profiles below as premises.

## Exact formal family

Use complete SM profiles of 10,bar5,40,50 and their conjugates. The convention
is fixed by formal characters 40=(5 tensor wedge²5 minus wedge³5)* and
50=Sym²(wedge²5) minus wedge⁴5. The standard integer hypercharges are 6Y.
The [independent checker](../../../tools/theorem-driven-protection-constraints/check_su5_exotic_bounds.py)
constructs the full weight characters, decomposes every spectator block and
reconstructs the original characters exactly. Dimensions 10,5,40,50 and the
Lean literal profiles agree. These are formal character calculations, not
proved continuous branching equivalences or an actual kernel construction.

For net counts n=(net10,netbar5,net40,net50), source-minus-conjugate-partner
counts are:

| Species | Formal excess |
| --- | --- |
| Q | net10 + net40 |
| uc | net10 + net40 |
| ec | net10 |

An SM-only dual index with N generations and no extra chiral spectator
content has four necessary rows:

- ec forces net10=N;
- L forces netbar5=N;
- the color octet, weak singlet at 6Y=6 forces net40=0;
- the charged singlet at 6Y=12 forces net50=0.

The last singlet is not a gauge singlet because its hypercharge is nonzero.
Gauge-neutral singlets do not affect these rows. Vectorlike extra pairs are
allowed at the index level. These conditions are not necessary for every
phenomenologically viable SM extension: an extension with other chiral
content is outside the declared target.

[ExoticCopyIndexBounds](../../../GUT/SU5/SelectionRules/ExoticCopyIndexBounds.lean)
proves `row_dictionary` with kernel computation, `net_constraints`, and
`positive_surpluses` for arbitrary signed net coefficients and positive N.
No finite copy cutoff is used. These prove index algebra on explicit supplied
profiles; they do not import the script as a proof premise.

## What is closed and what is not

| Obligation | Result |
| --- | --- |
| Complete-character decomposition, spectators and reconstruction | Exact reproducible Python check |
| Four-row formal index and variable-copy constraints | Lean proved |
| Positive formal Q/U/E excess under that target | Lean proved |
| Actual continuous SU(5) 40/50 branching equivalences | Not found among existing assets; not proved here |
| Arbitrary invariant mass presentation on the actual extended carrier | Not found; species embeddings and pairing classification still needed |
| Physical nonzero qque for all such masses | Not established by this continuation |
| A newly useful UV search region outside prior no-go coverage | Not demonstrated |

Thus the symbolic constraint computation is feasible without picking a mass,
but the proposed physical exclusion endpoint cannot be closed by existing
assets alone. The generic `SpeciesSectorPresentation` constructor does not
manufacture the extended carrier's decomposition and NoPairings evidence.
The earlier split-SU5 study likewise explicitly retains the original 40/50
branching and UV mass formulas as literature data.

The standard-chain theorem would already obstruct the compatible commuting
pure-target charge class. This calculation must not be counted as independent
new coverage of that class. Gauge-only allowance of qque also does not dispute
a model's vanishing generated coupling or decay claim.

## Stop and next prerequisite

Stop rather than introducing a wrapper that assumes the missing actual bridge.
Further physical progress requires a separately scoped actual branching
construction for 40 and 50, followed by complete opposite-species and pairing
classification for their arbitrary invariant masses. New scalar/VEV, residual
parity, UV coupling realization, anomalies and matching are separate questions.
No useful cost estimate for these foundations is inferred from the short
formal-index proof. The script and strict audit are retained as bounded evidence.
