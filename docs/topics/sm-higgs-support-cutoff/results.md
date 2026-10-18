# Uniform Finite Reduction Result

## Exact statement

The implementation reduces support at every fermion content and every
Higgs/dual count to a fixed finite table of actual invariant coefficient
spaces. Residual flavor actions remain parameters. No entry's nonzero
support is assumed merely from its charge or weak degree.

For a species pattern p, define N_p as its number of weak doublet slots and
Y_p as its integer hypercharge sum. Signed dual doublets also count once.
Let delta=h-d in integers and

    T(p,m,delta) = Hom_Gamma(W_p tensor
      [z^(3*delta) twist of pulled-back Sym^m(doublet)], C).

W_p is the image of the actual species-slot tensor in the full exterior
source. Exterior statistics, including zero images, are retained. The
source is constructed, not supplied as a missing correspondence premise.
`PatternExteriorSource.orbit_iff_counts` identifies a pattern orbit with
its species counts, so patterns provide a redundant content dictionary.

`SMFiniteHiggsSupport.mem_original_iff` identifies `OriginalSpace` with
independent fermion-count and scalar-count support constraints on the
original full exterior/symmetric coefficient carrier. `originalEquiv`
constructs both directions of its connection to W_p; no raw ordered tensor
is substituted for W_p.

`original_charge_finite_iff` proves:

    Allowed(OriginalSpace(p,h,d)) iff
      Y_p + 3*delta = 0 and
      exists m : Fin(N_p+1),
        Admissible(h,d,m) and Allowed(T(p,m,delta)).

`Admissible(h,d,m)` is the exact natural-number predicate

    m <= h+d and h <= d+m and d <= h+m and (h+d-m) % 2 = 0.

Equivalently, |delta| <= m <= h+d with the same parity as h+d.
The scalar twist and all color/Weyl/residual constraints stay in T.
`original_forbidden_iff` proves the negated finite predicate.

## Degree-independent table and stability

`original_table_iff` indexes the tests by s,t in Fin(N_p+1), with
s+t <= N_p. The test has m=s+t and delta=s-t. Original counts (h,d)
only filter this fixed table by their difference and admissibility.
`BoundedHiggsSupport.representativeEquiv` identifies each test's boson
representation with the r=0 constituent at representative counts (s,t).
It does not identify the whole representative coefficient space with
that one constituent.

`original_imbalance_forbidden` excludes |h-d|>N_p.
`original_pair_monotone` proves upward support under adding one H/dual pair.
For |delta|<=N_p, once

    min(h,d) >= floor((N_p-|delta|)/2),

`original_pair_stable` and `original_pairs_stable` prove support is unchanged
under one or arbitrarily many further pairs. In Lean the absolute difference
is written `(h-d)+(d-h)` with explicit parentheses and natural subtraction.
This is a sufficient uniform threshold; an individual source can stabilize
earlier. These proofs use actual constituent equivalences, not downward
inference from dressing monotonicity.

## Fixed finite universe

The existing 180-dimensional three-generation input gives zero exterior
coefficients above fermion degree 180, and N_p<=degree(p).
`SMFiniteSupportTable.all_degrees_iff` handles every fermion degree, including
the zero cases above 180. `global_table_iff` uses an actual Fintype index:

    [n : Fin 181; p : Fin n -> Fin 10] x Fin 181 x Fin 181.

This finite superset deliberately keeps repeated content orderings and
entries later rejected by the filters. It proves a finite reduction, not
an enumeration or executable classification of the Hom entries. No
finite-generation theorem or source semisimplicity is required.

## Weight proof and controls

The actual signed gauge bases have weak weights zero or plus/minus one.
Weyl and supplied flavor factors contribute zero. The typed tensor basis
has weights between -N_p and N_p, and its surjection onto W_p transports
this spanning bound. `source_dual_eigen_zero` excludes dual eigenvectors
outside the same interval. The generic `high_spin_hom_zero` uses the pinned
actual SU2 irreducibility and nonzero highest-weight basis vector to show
that Sym^m -> dual(W_p) is zero for m>N_p. Dimension 180 is used only for
the finite fermion universe, not as an unsupported weight argument.

The two-Q pilot has N_p=2 and Y_p=2. Its all-degree support is forbidden by
the integral equation 2+3*delta=0. The generic finite reduction also applies
to this nontrivial weak source; no positive-witness premise was added.

Kernel-checked convention controls for DUQL, QQUE, QQQL, DUUE, uR^2 dR^4 and
LL give respectively N_p=(2,2,4,0,0,2) and Y_p=(0,0,0,0,0,-6). Thus the
neutral families require h=d and LL requires h=d+2, consistently with their
previous results. Their individual residual/witness classifications are not
reproved or premises of this uniform theorem.

## Remaining boundary

The selected finite-reduction endpoint is proved and its acceptance checks
passed, as recorded in [verification](verification.md). `Allowed(T)`
remains an actual invariant-Hom predicate. Deciding those tests for existing
q/l actions, revisiting 572 assignments, or classifying other residual
groups was not required or started at this endpoint checkpoint. Subsequently,
[existing q/l extraction](../sm-rank-certificates/ql-extraction-results.md)
proved the support criterion under explicit Weyl input; concrete numerical
evaluation and other residual classes remain separate.

The input still has one neutral-residual Higgs doublet/dual, ten signed SM
species with three-dimensional flavor carriers and the existing gauge/Weyl
dictionary. Derivatives/EOM/IBP, additional Higgs copies/actions, masses/VEVs,
UV/quantum realization, matching and rates remain outside the result.
