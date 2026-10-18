# Four Fixed Fermion Families at Every Higgs Degree

## Exact result

For the actual three-generation signed SM/Weyl input, universal physical
cyclic charges (q,q,q,l,l), every positive cyclic order k and neutral one-copy
Higgs/dual fields, each of the four fixed contents obeys

    allowance iff h=a and 3q+l=0 mod k,
    prohibition iff h!=a or 3q+l!=0 mod k.

Here h and a count Higgs and algebraic dual-Higgs fields. These are whole
fixed-content coefficient spaces on actual exterior-four/symmetric-(h+a)
carriers, not images of dressing maps. Color, Lorentz, weak and statistics
invariance are part of the existing actual representation dictionary.

| Family index | Fermion content | Zero-Higgs witness coordinates |
|---|---|---|
| 0 | DUQL | Four distinct-species flavor coordinates |
| 1 | QQUE | Actual symmetric quark-pair coordinates |
| 2 | QQQL | Actual sorted symmetric, alternating and mixed Young coordinates |
| 3 | DUUE | Actual residual dictionary retaining repeated up-fermion statistics |

[FourFamilyHiggsContent](../../../Physics/StandardModel/Operators/FourFamilyHiggsContent.lean)
is the shared implementation. Indices selects each statistics-aware coordinate
space. baseEquiv transports through the four previously proved physical
family equivalences, and indices_nonempty_iff proves a neutral coordinate
exists in every family. For QQQL the explicit witness belongs to the sorted
symmetric branch; raw ordered triples are not assumed independent. Other
Young branches remain in the complete dictionary rather than being discarded.

## Common proof route

- Define species support before choosing any contraction seed, and prove its
  permutation stability and actual coefficient projection.
- Use actual hypercharge invariance and zero fermion hypercharge in every
  family to force h=a whenever a selected value is nonzero.
- Use actual cyclic residual actions and the common total charge 3q+l to
  derive the necessary neutrality condition.
- Reconstruct a nonzero zero-Higgs coefficient through each actual family
  dictionary, dress with the already certified invariant pairing power,
  and prove the result belongs to the full balanced content and is nonzero.

The shared proof takes the family index as data. Its family-specific inputs
are the certified species counts, charge sums and the actual statistical
coordinate equivalences. It is not a fermion-number induction or a theorem
asserting that every new content has the same support.

## Simultaneous selection

CombinedSpace is independently defined by the union of these four content
predicates. combined_forbidden_iff proves prohibition of this actual space
iff prohibition of each component. The cyclic union therefore has the same
fixed-count support iff. all_four_forbidden_iff proves

    all four contents forbidden at every Higgs count iff 3q+l!=0 mod k.

This union includes all selected contractions in those four contents. It
is not the full all-degree B1 sector: additional fermion counts and other
four-fermion contents with Higgs-compensated hypercharge are not classified.
DUQL remains a definitional control through duql_control; its older public
proofs were preserved.

## Endpoint and remaining boundaries

The authorized extension to QQUE, QQQL and DUUE is complete. No VEV, mass,
UV lift, semisimplicity or coefficient nonzero premise was added. No finite
invariant-ring generator list or coefficient-spanning claim is established.
The [uniform support boundary](support-boundary.md) still applies to other
contents and to finite covariant generation. The earlier 572 labeled charge
assignments and 151 orbits are unchanged: the new statements strengthen the
proved domain of the existing arithmetic predicate rather than recount it.

The [contract](four-family-contract.md), [sources](references.md) and
[verification](verification.md) record scope and checks. Actual allowance
means an available invariant coefficient, not a generated interaction,
anomaly-free model, decay amplitude or rate. No master merge or push was done.
