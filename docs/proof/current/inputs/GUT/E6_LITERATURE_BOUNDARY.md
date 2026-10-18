# E6 Literature-Assisted Topology

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

External reference roles and the stage 02 bibliographic checks are recorded
in the [individual reference review](../../../REFERENCE_REVIEW.md).

## 1. Result and status

Updated: stage 01

### Decision And Exact Status

The user approved external, established mathematical theorems in place of
developing the missing topology foundations. Leanstral delegation is stopped.
This changes the verification boundary, not the physical model assumptions.

**Kernel checked:** the implication from a named literature input to simple
connectedness of the actual `compactIdentityComponent`. The external input
has no supplied proof, global axiom, or implicit instance. All consumers
retain it as an argument. An axiom audit of that implication does not prove
the premise.

**Literature-assisted mathematics:** maximal-torus surjectivity supplies that
input. The named compact simply connected E6 interpretation additionally uses
the classical Lie-algebra/group classification described below. Neither
external step is claimed as an unconditional Lean theorem.

## 2. Inputs and conclusion

### External Topology Input

Raghunathan's lectures, Proposition 38, state that inclusion of a maximal
torus in a compact connected Lie group induces a surjection on fundamental
groups. We use only this surjectivity, not the kernel computation.
[Source, PDF page 37](https://www.atmschools.org/sites/default/files/Lecture-notes-1-13.pdf#page=37).
The notes identify their typist and say the lecturer had not proofread them;
the needed surjectivity is explicitly derived from Proposition 37 and the
quotient fibration. We do not rely on the omitted reverse kernel inclusion.

The typed interface is `GUT.Topology.MaximalTorusSurjectivityInput E G` in
[MaximalTorusFundamentalGroup](../../../../../Math/Topology/MaximalTorusFundamentalGroup.lean).
It requires a finite-dimensional real model space, a Hausdorff compact
connected smooth Lie group, and quantifies over `MaximalTorusData G`.
Each datum is a continuous closed embedding of a finite product of circles,
maximal among Abelian subgroups. This stronger maximality implies maximality
among tori; normality is never required.

The input directly concerns the map from that product of circles, avoiding
an unproved identification of a different quotient or coordinate map. In
ordinary mathematics it is the range-inclusion theorem transported along
the homeomorphism from the closed embedded torus onto its range. This
reparametrized version is part of the external statement, not a separately
claimed Lean proof of the general literature theorem.

## 4. Proof structure

### Actual Application

| Requirement | Checked source |
| --- | --- |
| Compact, connected, Hausdorff candidate | Existing component instances, tested in the new audit |
| Finite real dimension and actual smooth Lie structure | `compactMatrixLieAlgebra`, `compactLieGroup` |
| Closed embedded six-circle torus | `Torus.hom_continuous`, `Torus.hom_closedEmbedding` |
| Maximality | `Torus.maximal_abelian`, derived from the checked self-centralizer |
| The actual based map | `Torus.maximalTorusData_fundamentalMap`, proved by `rfl` |
| Every torus loop contracts in the candidate | `Torus.fundamentalMap_apply_eq_one` |
| Path connectedness of the candidate | `compactPathConnected` |

[FundamentalGroupSurjectivity](../../../../../Math/LieGroups/E6/Minuscule/FundamentalGroupSurjectivity.lean)
proves, with explicit `hLiterature : TorusSurjectivityLiteratureInput`:

1. `fundamentalMap_surjective_of_literature`;
2. `fundamentalGroup_eq_one_of_literature`;
3. `compactSimplyConnected_of_literature`.

For any class c, surjectivity gives c = j(a); the existing contraction theorem
gives j(a) = 1. Path connectedness and basepoint transport then establish
simple connectedness. The torus itself is not asserted simply connected.
L5-L7 are not hypotheses of these proofs and are not imported.

## 6. Scope and limitations

### Named E6 Interpretation

The candidate's actual geometric Lie algebra is already identified with the
skew-Hermitian real form by `compactTangentRealFormLieEquiv`. Its complexification
is identified with the pinned Geck E6 algebra by `compactGeckEquiv`.
These are concrete existing comparisons, not new certificates.

To interpret this as the conventional compact simply connected E6, ordinary
mathematics also uses classification of compact real forms and uniqueness
of a simply connected Lie group with a specified real Lie algebra.
Etingof's notes give the Lie correspondence in Theorem 9.12/Corollary 9.14,
real-form classification in Sections 40-41, and compact-group classification
in Section 43. This yields the named-group interpretation from the checked
local comparisons and the literature-assisted simple connectedness.
[Lie correspondence, PDF page 56](https://ocw.mit.edu/courses/18-755-lie-groups-and-lie-algebras-ii-spring-2024/mit18_755_s24_lec_full.pdf#page=56),
[real forms, PDF page 219](https://ocw.mit.edu/courses/18-755-lie-groups-and-lie-algebras-ii-spring-2024/mit18_755_s24_lec_full.pdf#page=219).

This last paragraph is a literature-assisted mathematical identification,
NOT a newly constructed Lean equivalence to an independently defined E6
carrier. Global integration/classification and that equivalence remain
outside the formalized boundary. Do not silently turn the candidate into
an unconditional named-E6 Lean instance.

### Physical Scope

The checked candidate SU(5) inclusion and supported selection-rule theorem
are unchanged and do not depend on this topology input. Under the above
literature interpretation they concern the corresponding chosen SU(5) chain
in compact E6. They do not quantify over every SM embedding or remove the
unitarity, invariant mass, exact dual light target, or ordinary Abelian action
hypotheses. No nonzero amplitude or finite proton lifetime is inferred.

## 7. Sources and verification

### Preservation And Audit

The rejected L5-L8 drafts are preserved under
[Leanstral review archive](../../../../topics/e6-global-topology/drafts/README.md),
not accepted as external results. Valid path/smoothness/regular-point proofs
and general helper lemmas are retained. The former L1-L4 completion claim
is corrected in [E6_status](../../../../topics/e6-global-topology/checkpoints/e6-reviewed-status.md).

`AuditLiteratureTopology` tests actual instances, exact map equality and
conditional consumers; its 14-declaration allowlist rejects `sorryAx`.
An additional negative test rejects accidental unconditional simple-connectedness
instance synthesis when the literature input has not been supplied.
It also checks retained local-prover results and is imported by `GUT.lean`.
Thus the default build now covers these additions.

```sh
lake build Math.LieGroups.E6.Audit.AuditLiteratureTopology
lake build
```

The first focused build passed (3984 jobs, including cached replay).
Final regression results are recorded in [historical milestone record](../../../../topics/e6-global-topology/checkpoints/e6-topology.md).
Stop at this boundary; implementing Proposition 38 or Lie integration is
not a task activated by this milestone.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
