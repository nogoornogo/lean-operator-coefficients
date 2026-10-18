# Connection Result: Exact Component Chain And Compatibility Obstruction

## Outcome

The literal, explicitly chosen all-left-handed component action is now connected
to the previously normalized actual light coefficient. Its neutral mixing is
computed from the same chi Yukawa coupling, rather than supplied independently.
Here y,Y are coefficients in the chosen holomorphic component chart; their
unchanged identification with the source's mixed-notation y_R is not proved.
The Grassmann mass-action half is proved and a restricted convention test gives
an exact obstruction. Full normalized agreement with the paper remains
unverified; the obstruction is not a paper-error theorem.

## Shared Fermionic Convention Certificate

[WeylGrassmannAction](../../../Physics/FieldTheory/Mass/WeylGrassmannAction.lean)
uses exterior generators g(i,s), with species i and two spin components s.
The bracket is g(i,0)g(j,1)-g(i,1)g(j,0). Anticommutation proves this bracket
is symmetric in i,j. Consequently the action with symmetric coefficient matrix
and factor -1/2 expands to

```
-d * bracket(0,1) - M * bracket(1,2) - (mu/2) * bracket(2,2).
```

These are actual Grassmann products, not commuting coordinate polynomials.
The existing Euclidean four-component C P_R adapter is extended to these
products and gives exactly this two-spin bracket. This fixes a concrete
four-component convention; it does not establish that the paper uses it.
No new gamma-matrix foundation or change of signature is claimed. Hermitian
conjugate terms are separate; their inclusion is not double counting the
holomorphic coefficient matrix. The helper and its layer/axiom audit are in
shared Physics, without PS imports.

## Explicit PS Component Chain

[SourceConnection](../../../GUT/PatiSalam/Matching/SourceConnection.lean)
selects h1=star(w), h2=0 and the conjugate Phi Yukawa yt=0. These are explicit
vacuum/coupling inputs, not consequences of the potential. The previously
checked Phi entry gives d=Y*star(w); the neutral chi contraction gives
M=y*star(v), using the same y as the colored vertex.

The action built from these two brackets equals the action of the previous
mu=0 symmetric matrix. `action_parameters` identifies that matrix with the
one consumed by the normalized coefficient construction. The parameter map
has no independently chosen M. The normalized kernel and light exterior
coefficient are connected using the supplied all-left-handed dictionary and
canonical kinetic form.

On Lambda,m,y,v != 0, the actual normalized light coefficient is nonzero iff
w,Y != 0 and at least one of C_L,C_R is nonzero. An exact nonzero control and
zero-UV control are proved. The UV origin of C_X remains external. This closes
mass/vertex consistency for this selected component action, not full PS
representation admission or all possible Higgs directions.

## What The Convention Test Establishes

For d,M != 0, the Lean theorem `common_factor_iff` states

```
k * mass(d,M,0) = mass(d,r*M,0)  iff  k=1 and r=1.
```

Here the left multiplication scales every matrix entry. The unchanged Dirac
entry forces k=1; the heavy entry then forces r=1. The real square root of two
is proved different from one. Thus, with a real component VEV and unchanged
d,y,v, no common overall mass-action factor converts M=y*v into
M=y*sqrt(2)*v. `no_common_factor_real_vev` applies this test directly to the
component parameter map.

This rules out one previously suggested repair: changing only the overall
mass factor, including the conventional 1/2, cannot fix a discrepancy confined
to the heavy entry. It does not rule out changes of coupling conventions,
kinetic normalization, relative field definitions, or other transformations.
It assumes nonzero Dirac entry and heavy mixing, as explicitly stated.

The pinned [source](https://arxiv.org/html/2211.02054v2), Eqs.(2),(10)–(14),
uses a sqrt(2) VEV definition together with a displayed mass entry whose full
translation remains unresolved. The formal incompatibility concerns the
specified literal same-parameter identification, not every possible reading
of these expressions. No erratum, experimental conclusion or refutation of
the paper is inferred.

## Remaining Admission And Stopping Decision

Derived: finite component contractions, shared Grassmann mass expansion,
selected mass/vertex parameter relation, normalized kernel and actual
coefficient nonzero criterion, restricted common-factor obstruction.

Supplied: explicit all-left-handed identification of source fermions,
canonical kinetic form, selected Phi direction/coupling, UV C_X and prior
component-sector admission. Unproved: full PS group-equivariant field maps and
the source's mixed four-component notation to this kinetic/mass dictionary.
The reused Euclidean C P_R identity is a convention certificate, not that map.

The [connection plan](connection-plan.md) stops at this exact component-chain
certificate and compatibility obstruction. An unconditional paper comparison
would require a specified field/kinetic/coupling transformation, and then proof
that it preserves both source vertices and the mass action. No such
transformation is manufactured to obtain agreement. Rates, finite-mu spectral
analysis and full proton stability remain outside scope.

See [verification](connection-verification.md) and the
[previous normalization result](follow-up-result.md).

## Subsequent Convention Comparisons

The [common-scale result](common-scale-result.md) tests the canonical source
chart and displayed light mode, rather than the older component chart above.
The [multiplet-rescaling result](multiplet-rescaling-result.md) tracks specified
whole-multiplet scalar changes and their simultaneous vertex/VEV substitution.
Neither certifies arbitrary kinetic conventions or full signed UV matching.
