# DUQL Higgs Covariants: Bounded Continuation Plan

## Authorization and branch

- Status: whole-content support and finite-seed consumer proved; actual finite spanning remains at the missing-certificate stop.
- User direction: plan the one-fermion-content covariant continuation.
- Working branch: proof/prohibition-converse-boundaries (existing approved branch).
- Base checkpoint for this continuation: checkpoint 01.
- Integration target: this branch; no master merge or remote push authorized.

This resumes stage 4B for one content only. It does not authorize a general
reductive invariant-theory library or the full stage 4C classification.
The [literature assessment](covariant-literature-assessment.md) and
[source register](references.md) retain the references and their limits.

## Frozen input and objective

Use the existing three-generation signed SM/Weyl fields, precisely one each
of the DUQL species, one Higgs doublet H and its algebraic dual H-dual.
Keep the actual color, weak, hypercharge, Lorentz and exterior/symmetric
statistics actions. Retain neutral scalar residual action and universal
cyclic physical charges (q,q,q,l,l), for every positive cyclic order k.
No VEV is chosen. Do not impose a numerical conjugation condition on the
independent algebraic H and H-dual fields.

The target is the whole coefficient space at this DUQL fermion content,
with arbitrary Higgs and dual-Higgs counts h,a. The already proved
DressedDuqlFamily is only a subspace and is a nonzero control, not the
candidate definition of the whole space. Include every flavor coordinate
and every contraction surviving the actual statistics carrier.

Prove a finite homogeneous spanning family over the scalar invariant ring,
then derive support and cyclic prohibition for every h,a. Full coordinate
bases or minimal generators are optional; spanning must be proved.

## Candidate reduction to verify

The proposed scalar invariant is t = H-dual(H). The candidate scalar ring
is C[t] for this one-doublet/one-dual input. Fermion hypercharge is zero,
so the proposed necessary Higgs condition is h=a. DUQL contains two weak
doublets, whose tensor product suggests weak singlet and triplet structures.
Candidate seeds therefore lie at scalar bidegrees (0,0) and (1,1), followed
by multiplication by powers of t.

These are conjectured reduction data, not assumptions or an already proved
cutoff. In particular, the triplet channel must be checked: the existing
DUQL times t^r family need not span every dressed DUQL coefficient. Do not
fix the number of seeds until color/Lorentz/statistics and flavor factors
are actually identified. Revise candidate degrees if an explicit surviving
channel disproves this proposal, and record the reason before proceeding.

## Milestones and dependencies

1. **Actual content carrier.** Define the DUQL fixed-content coefficient
   subspace in the existing mixed interface and split scalar h/a counts.
   Prove its relation to the typed exterior/flavor carrier; extract the
   color/Lorentz invariant factors and remaining weak representation.
   Endpoint: an actual equivariant dictionary, not a dimension count.
2. **Scalar multiplication.** Identify graded symmetric coefficients with
   polynomial covariants, fixing dual and normalization conventions. Define
   multiplication by t on the actual carriers and prove descent, invariance,
   bidegree shift (h,a) -> (h+1,a+1), and preservation of residual charge.
   Endpoint: a typed multiplication interface reusable for other contents.
3. **Concrete scalar and weak completeness.** Prove the scalar invariant
   description and all-degree weak covariants needed for the carrier in
   milestone 1. Prefer explicit two-doublet decomposition/contractions;
   use classical invariant theory as a guide. Prove that no other weak or
   hypercharge channel occurs. Endpoint: complete homogeneous spanning by
   the certified seeds and powers of t. Existence of general finite
   generation, a Hilbert series or sampled low degrees does not suffice.
4. **Support and cyclic criterion.** Establish actual nonzero seed/dressing
   witnesses and support iff at each h,a, including zero degree, unequal
   counts and repeated-flavor controls. The expected result is that DUQL
   support exists exactly at h=a, and cyclic allowance then additionally
   requires 3q+l=0. Prove this expectation or record a counterexample; do
   not replace it by the smaller already certified family. Connect actual
   coefficient prohibition to the existing symmetry/charge interfaces.
5. **Verification and record.** Register new Math/Physics files and strict
   transitive audits in the appropriate aggregates. Run focused builds,
   strict audits, a serialized full lake build, layout, links and diff
   checks. Update results, boundaries and assumptions only for proved
   statements. Commit coherent verified milestones on the topic branch.

Milestones 1 and 2 determine the exact Lean statements before milestone 3
implementation. Inspect linked source declarations before naming new APIs;
no general algebraic-group representation infrastructure is assumed present.

## Stop conditions and decisions

Successful endpoint: finite spanning and exact support/charge iff for the
full fixed DUQL content at arbitrary Higgs counts, with actual carrier
transport and strict audits. This is one-content stage 4B progress, not a
classification of the other fermion contents or of all-degree B1 protection.

Stop and request scope judgment if the required proof demands a general
reductive invariant-theory foundation, changed dependencies, a different
field alphabet or new physical assumptions. If the concrete route fails,
record the precise missing statement and verified partial interfaces; do
not claim finite generation or support from a conditional theorem alone.
Candidate seed failure is a mathematical finding, not permission to add
an unproved completeness premise. No reliable duration is assigned until
the actual carrier and uniform weak decomposition are established.

## Source and scope policy

Use Grinstein et al. section 2.2.4 for covariant module structure and
relations, and the explicitly recorded finite-generation citation as
mathematical context. Treat Erickson--Hunziker as a candidate constructive
source: inspect its full relevant theorem and hypotheses before applying
it. Record theorem locations and conventions as they are checked.
Neither paper is a custom axiom or an automatic Lean certificate.

Exclude VEV/mass-spectrum classification, derivatives/EOM/IBP, UV matching,
anomalies, quantum effects, rates and enumeration of new UV models.
Preserve the existing 572 assignments and 151 orbits until a separately
approved all-content criterion justifies changing them.

## Recorded endpoint

The [outcome](duql-content-results.md) separates the completed whole-content
support iff from the unproved finite-spanning objective. Hypercharge and
residual obstructions plus a certified dressing witness suffice for this
content's support, without invoking generation. The concrete uniform weak
covariant spanning theorem remains the stop boundary.
