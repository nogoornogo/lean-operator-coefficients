# Actual Compact Torus in the E6 Candidate

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

## 2. Inputs and conclusion

### Frozen Endpoint

**LEAN-CHECKED:** an actual closed embedding of `Fin 6 -> Circle` into
`compactIdentityComponent`, with Cartan exponential kernel `2 pi Z^6`
and self-centralizing image. This supplies the actual maximal torus and
its period lattice for the chosen global-form route. It is not the
missing identification of the fundamental group with a coroot quotient.

The user requested continued work after the exact-center milestone
`checkpoint 01`. All group definitions, physical assumptions, dependency pins,
and existing proofs are preserved.

### Interfaces and Bound

1. The minuscule weight characters define a continuous injective six-circle
   homomorphism into the actual candidate. Membership must follow from
   actual real Cartan exponentials. Compute their exact kernel, not just
   an upper or lower period bound.
2. Use the already proved cubic invariant to reconstruct every diagonal
   candidate element from six independent weight coordinates. Finite
   coordinate tables must be checked in Lean against the actual weights
   and cubic, not accepted from an external solver.
3. Prove that centralizing this torus forces a matrix to be diagonal,
   hence the centralizer equals the torus image. This implies that no
   larger Abelian subgroup, and in particular no larger torus, contains it.

Allowed tools are the existing Cartan matrices, cubic, exponential and
scalar analysis APIs, finite integer checks, and subgroup topology.
No general Lie integration, root classification, covering construction,
or fundamental-group calculation is part of this package. If one becomes
necessary to close these interfaces, preserve work and report that blocker
instead of starting another foundational milestone.

## 6. Scope and limitations

### Acceptance and Exit

All three interfaces are closed:

- [TorusCoordinates](../../../../../Math/LieGroups/E6/Minuscule/TorusCoordinates.lean) checks
  that the weights at `2,3,4,9,21,23` form an integral basis, with both
  matrix-inverse identities checked in the kernel. `recover_weights`
  supplies the actual left inverse to the 27 weight characters.
- [CompactTorus](../../../../../Math/LieGroups/E6/Minuscule/CompactTorus.lean) constructs
  `Torus.hom` using actual Cartan exponentials in the candidate. The matrix
  is precisely diagonal with entries `product z_i ^ weight(a,i)`.
  Continuity is proved from this matrix formula, not from continuity of
  the chosen arguments of circle points. `hom_closedEmbedding`,
  `subgroup_isCompact` and `subgroup_isConnected` give the actual torus.
  `exp_direction_eq_one_iff` gives exactly `2 pi Z^6` in the six Cartan
  coordinates, using injectivity and the circle exponential period theorem.
- [CubicTorusReconstruction](../../../../../Math/LieGroups/E6/Minuscule/CubicTorusReconstruction.lean)
  extracts 21 equations from the actual invariant cubic. Restricting the
  cubic to each three-coordinate support is checked as a finite integer
  certificate. A checked acyclic elimination order reconstructs all 27
  diagonal phases from the six seed coordinates. `diagonal_reconstruction`
  identifies every diagonal candidate element with an element of `Torus.hom`.
- [TorusCentralizer](../../../../../Math/LieGroups/E6/Minuscule/TorusCentralizer.lean)
  differentiates commutation along the six Cartan exponential lines.
  The existing Cartan commutant lemma forces diagonality; the preceding
  reconstruction then gives `centralizer_eq`. `maximal_abelian` proves
  that any Abelian subgroup containing this torus equals it, hence in
  particular there is no larger containing torus. This statement concerns
  subgroups of the actual candidate, not an ambient GL normalizer.

The finite tables were found by exact arithmetic on the weight/cubic
data. They are not trusted inputs: their inverse identities, cubic
restrictions, elimination inequalities and coordinate coverage are all
checked in Lean. The matrix and group comparisons are proved separately.

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactTorus
lake build
```

The [persistent audit](../../../../../Math/LieGroups/E6/Audit/AuditCompactTorus.lean) checks
29 declarations with only `propext`, `Classical.choice`, `Quot.sound`.
It also tests that a half period is not a full period, that the order-three
center element belongs to the torus, and that the ambient order-27 scalar
remains outside the connected candidate. Targeted: **3897 jobs / 29 reports**.
Full: **5497 jobs / 2554 reports** (2553 lists and one axiom-free report).
New modules are warning-free; dependencies and physical assumptions are unchanged.

**Stop gate reached.** The remaining global route needs a proved comparison
between this actual torus's geometric coroot data and the candidate group's
fundamental group, or a covering construction with trivial kernel. This
package does not compute the latter group or assert simple connectedness.
The intended global E6 identification remains open; no additional foundation
is automatically queued by the successful torus construction.

The later bounded [coroot-loop package](E6_COROOT_LOOPS.md) constructs
based contractions of the six coordinate loops inside the candidate.
The subsequent [all-torus-loop package](E6_TORUS_LOOPS.md) contracts every
identity-based torus loop in the candidate and proves the induced
fundamental-group map trivial. Surjectivity of that map remains open.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
