# Complete B1 support below dimension ten

## Exact criterion and scope

For every positive cyclic modulus k and q,l in ZMod k, the fixed
three-generation signed SM dictionary admits an actual derivative-free B1
coefficient at engineering dimension strictly below ten iff

`3*q+l=0 ∨ 3*q-l=0 ∨ 3*q+3*l=0`.

The equations live in ZMod k. `SMB1BelowTen.Allowed` is existence of an
original coefficient space with absolute B3=3 and `3*n+2*(h+d)<20`.
`Forbidden` universally excludes actual coefficients on that same domain;
the complement equivalence and complementary three-nonzero criterion are
proved. Both baryon signs, all species contents and every Higgs bidegree
under the grading bound are retained. This is a bounded support theorem,
not all-degree B1 protection or an all-input minimum-dimension formula.

## Why the finite reduction is complete

Charge-degree and the grading bound force absolute L≤3. Actual Lorentz
parity makes L odd. The existing proved hypercharge envelope and actual
hypercharge neutrality exclude normalized L=-3 below ten: this charge would
need n≥6, so n=6 and h=d=0, contradicting the hypercharge envelope. The
remaining normalized charges are L=1,-1,3. The proof handles actual B3=3
and B3=-3 directly; no source-conjugation or dimension-preservation premise
is assumed. Thus no occupation/content enumeration is needed for necessity.

All three remaining charge possibilities have original-space witnesses:

| Normalized L | Pattern | (n,h,d) | Dimension |
| ---: | --- | --- | ---: |
| 1 | Q³L | (4,0,0) | 6 |
| -1 | uR dR² conjugate(L) | (4,0,1) | 7 |
| 3 | uR³L²eR | (6,0,0) | 9 |

The second pattern includes a dual Higgs. Each family reuses an actual
positive **joint** color/weak/two-spin certificate, generation occupations
and statistics, and reconnects the fixed pattern with arbitrary neutral
q/l action through `original_ql_iff`. Reusing the older ungraded existential
allowance theorem alone would not prove these dimension statements.

Route A closes all candidates. Route B and exhaustive content search were
not needed; there is no unresolved row or resource stop. The arbitrary-k
helper is the same finite proof allowed by the frozen plan, not a separate
classification of general flavor actions.

## All 572 assignments

The existing Lean-owned `rows`/`keys` are reused unchanged, with unique
coverage of `2≤k≤12`, `q,l<k`, `(3*q+l)%k≠0`. Hence the first congruence is
excluded in this domain. `domain_allowed_iff` leaves exactly the other two.
`row_decision` proves an actual semantic verdict for each row. The counted
Boolean predicate is equivalent to bounded original-space allowance; its
false branch is equivalent to universal bounded prohibition.

| Verdict | Count |
| --- | ---: |
| B1 allowed below ten | 146 |
| B1 forbidden below ten | 426 |
| Of the 426: allowed at some degree | 180 |
| Of the 426: forbidden at every degree | 246 |

All four counts are kernel-proved in the default library build, and
`exhaustive_count` links their bounded partition to the 572-row length.
The two refined classes have proved semantics using the existing all-degree
classification. No CSV/table is read or supplied as a premise. An initial
lightweight Python count proposed 146/426 before the Lean count; it is not
the evidence for this classification and no script output is imported.

The (5,1,1) input is a strict-boundary control: it is forbidden below ten
and has proved minimum dimension ten. Thus bounded prohibition must not be
reported as full protection. Other importing consumers exercise dimensions
six, seven and nine, negative baryon sign and the refined row semantics.

## Verification and limitations

The new Physics sources, examples and audit are registered in the aggregate.
The persistent audit requires the criterion, complement, row verdict, count
and coverage declarations and checks all declarations in the three new
namespaces, including generated helpers, transitively against exactly
propext, Classical.choice and Quot.sound. It passes 69 checks.

New closed computations use kernel checking; ordinary algebraic proofs
establish necessity and transport. No `native_decide`, new axiom, audit
exception, dependency, option change, numerical oracle or multiplicity
premise is introduced. Old support definitions and assignment tables are
unchanged. RGE, derivatives/EOM/IBP, UV generation and rates remain outside
scope, as do B2 below-ten classification and higher-dimensional optimization.

The [verification record](verification.json) retains commands, source hashes
and sampled resources. All runs use one Lean thread, a 300-second guard,
10 GiB sampled process-group RSS and 4 GiB available-memory reserve.
No development proof failed or resource cap was breached.

| Accepted check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Criterion and three fixed witness families | 5.3 | 5235048 |
| All assignment semantics and kernel counts | 7.5 | 5599628 |
| Importing examples and persistent audit build | 7.3 | 5205428 |
| Direct audit re-execution: 69 strict checks | 4.3 | 5125392 |
| Fresh importing consumers, direct elaboration | 3.5 | 5110428 |
| Full default-root `lake build GUT`: 7352 jobs | 8.3 | 6704528 |

The full build has zero warnings/errors and includes the unchanged parent
minimum and earlier finite-charge/degree audits alongside the new audit.
Layout passes 1966 modules; source-policy and diff checks pass. Local-link
counts are retained in the verification record. Dossier, assumptions ledger
and source agree. Existing tables/definitions/pins remain unchanged, so their
unrelated optional regression exporters were not rerun. The full-build peak
is repository checking, not a generic search-performance theorem.

The frozen endpoint is complete: every one of the 572 assignments has a
bounded actual-coefficient verdict and no unresolved candidate remains.
The child was [integrated](integration.md) into its recorded non-master parent
at `checkpoint 01`, with fresh direct child/parent audits (69+140 checks) and a
successful full cached build. The local child branch was safely deleted.
No master integration, remote push or publication is authorized.
