# Four exact minimum operator dimensions

## Mathematical result

All four cases in the [frozen plan](plan.md) have exact minima. The fixed
three-generation signed SM, derivative-free statistics, independent Lorentz
actions, neutral-residual Higgs/dual and scalar cyclic q/l action are unchanged.

| Case | (k,q,l) | Sector | Minimum doubled dimension | Minimum dimension | Attaining pattern | (h,d) |
| --- | --- | --- | ---: | ---: | --- | --- |
| C1 | (2,0,0) | B1 | 12 | 6 | Q³ L | (0,0) |
| C2 | (2,0,0) | B2 | 18 | 9 | uR² dR⁴ | (0,0) |
| H1 | (3,1,1) | B1 | 18 | 9 | uR³ L² eR | (0,0) |
| H2 | (5,1,1) | B1 | 20 | 10 | dR³ conjugate(L)³ | (0,1) |

These pattern names denote species content, not an explicit contracted
Lagrangian monomial. Lean checks positive joint color/weak/two-spin support
with three-generation occupations and full statistics, then transports it to
the actual original coefficient space. The H2 pattern additionally has one
dual Higgs. No separate-factor invariant heuristic is used.

`IsMinimum` packages actual attainment and a lower bound for **every**
selected original allowed content, both signs of B3 and every Higgs bidegree.
`IsMinimum.unique` proves uniqueness; `forbidden_below` derives prohibition
at every smaller doubled dimension. Values are not minima over just the
chosen witness family or over a finite search window.

## Proof routes

Route A suffices for C1/C2/H1. The computed minima of absolute L are 1/0/3;
the previous uniform degree bound gives doubled dimensions 12/18/18, and
the displayed witnesses attain them. Existing charge witnesses for C2/H1/H2
were not assumed optimal: their Higgs or extra-fermion costs are avoided by
the new explicit supported patterns.

H2 has minimum absolute L=3 and charge lower bound D≥9, but that bound is
strict. Route B follows the [pre-recorded gap contract](gap-contract.md).
The dictionary inequality `abs(Y-B3+6L)≤3` per species sums to
`abs(Y(p)-B3(p)+6L(p))≤3*n`. Below doubled dimension 20, even fermion degree
and n≥6 force n=6,h=d=0. Charge-degree, parity and cyclic neutrality leave
(B3,L)=(3,-3) or (-3,3). Hypercharge neutrality would then force 21≤18.
Lean proves the bound symbolically for both signs, without content or
occupation enumeration in the negative direction. A source-conjugation
theorem is not assumed.

## Implementation and trust

The source, fresh importing consumers and persistent audit are registered in
Physics. The strict audit checks every declaration under the implementation
and example namespaces, including generated helpers, and explicitly requires
all four minimum theorems. It accepts exactly propext, Classical.choice and
Quot.sound; no custom axiom or exception is introduced.

Closed finite witness/count/charge calculations use the existing opt-in
decisions and `decide +kernel`. Their acceptance is kernel checking plus the
ordinary full-support/original-space semantic bridge. The universal bounds
use algebraic lemmas and ordinary `omega` certificates. No `native_decide`,
CSV input, numerical oracle, supplied occurrence premise or new reflection
engine is used. Unchanged existing definitions do not require regenerating
the historical 572-row checks.

Importing consumers include all four minima, explicit negative-B3 H2 use,
H2 scalar-free six-fermion prohibition, and rejection of both incorrect H2
minimum values 18 and 22. These exercise the domain and attainment boundaries.

## Development failures

The first focused build failed from missing local opt-in joint-decision
instances (5.8 s, 5259952 KiB). Adding the existing local-instance pattern
resolved it; witnesses and C1/C2/H1 then passed (6.8 s, 5308972 KiB).
Two H2 proof drafts failed: the first left absolute-charge terms opaque to
arithmetic (7.3 s, 5324820 KiB); after exposing that bound, the second still
omitted the existing B3+L parity consequence (6.8 s, 5325096 KiB). Adding
the actual parity theorem closed the argument. These were elaboration/proof
failures, not logical exclusions, successful proofs or resource stops.

An initial auxiliary policy scan matched the words `axiom ` inside the audit's
error message. A declaration-aware scan passes; this was a textual-check
false positive, not a custom axiom or an audit exception.

The accepted focused audit build passes in 12.3 s at 5346400 KiB sampled
group peak, with 140 strict transitive checks and zero warnings/errors.
Final acceptance checks and resource measurements are recorded separately
below and in [machine-readable evidence](verification.json).

## Final acceptance

All runs use one Lean thread with the frozen 300-second, 10 GiB sampled
process-group RSS and 4 GiB host-reserve guard, unchanged pins/options and
cached imports. No run hit a resource limit. The guard command and exact
source hashes are retained in the JSON record; disposable logs stay in /tmp.

| Accepted check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Focused module/examples/audit build | 12.3 | 5346400 |
| Direct audit re-execution: 140 strict transitive checks | 4.0 | 5121772 |
| Fresh importing consumers, direct Lean re-elaboration | 3.5 | 5085748 |
| Full default-root `lake build GUT`: 7348 jobs | 8.5 | 6708832 |

The full build passes with zero warnings/errors and includes the new audit
alongside the unchanged 1199 finite-charge, 52 minimum-lepton and 13 base
degree checks. Fresh consumers are re-elaborated applications, not `#check`
on cached results. All four original-space minimum certificates are complete.
The approximately 6.40 GiB full-build peak measures repository checking, not
a generic support-search runtime bound.

Layout passes 1962 modules. Final local-link and diff checks are recorded
in the topic overview. The source, assumptions ledger and application dossier
agree on the four inputs, all-content/all-Higgs lower bounds and physical
limits. Existing support definitions, generated tables and dependencies are
unchanged. This is the planned endpoint; no unresolved case remains.

## Scope and follow-up boundary

This completes only the four planned exact minima and reusable semantic
certificate. It does not optimize all 572 assignments or prove an all-k
minimum-dimension formula. The hypercharge inequality is reusable for the
same dictionary, but no broader classification is inferred. No new foundation,
dependency, Lean limit, all-content solver, derivative/EOM/IBP extension,
UV generation, anomaly analysis or rate calculation is included.

The other three user-selected follow-ups remain deferred. No master merge,
push or publication is authorized by this endpoint.
