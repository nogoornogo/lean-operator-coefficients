# External-library assessment for A2 and mixed contents

Reviewed stage 01 on `proof/sm-rank-certificates`, after `checkpoint 01`.
This is source inspection and a bounded compatibility assessment, not a new
A2 theorem or authorization to change dependencies. The existing Lean and
mathlib/TauCeti pins are unchanged.

## Required interfaces

1. Identify the actual mixed statistical source with the tensor product of
   species exterior powers, preserving signs, multiplicities and group action.
2. Extract SU3 invariant multiplicity from the finite torus character by the
   positive-root constant-term functional, for the actual generated sources.
3. Preserve the actual independent left/right Weyl actions when passing to
   compact factors. A diagonal compact restriction is not sufficient.

An abstract character identity, a highest-vector existence theorem, a root
system or an assumed decomposition does not by itself close these interfaces.

## Snapshots and compatibility

| Candidate | Inspected revision | Lean | mathlib revision |
| --- | --- | --- | --- |
| Existing mathlib | `1a547d8a48a8fa7877d2decb69d7294723bb0187` | project: `v4.35.0-rc3` | same |
| Existing TauCeti | `b9e2e182804073eb92718b68a9baf37df8e189bd` | project pin | project pin |
| ATLAS root | `8004bc185206d3d34cc6a7cf0840edca89cf64ce` | `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| ATLAS v1 at the same revision | same | `v4.29.0` | `8a178386ffc0f5fef0b77738bb5449d50efeea95` |
| LeanPool | `01db1d7049cf9668bda1e9e106875ee1278b43e6` | `v4.35.0-rc3` | `c55e6e786f49471c72fbddbec5415808896aec1e` |
| Physlib | `c3964f48db4b861c8ebe706d8ff6febe07025827` | `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

Matching Lean versions does not establish matching mathlib APIs or a safe
combined Lake graph. No external package was installed or built as a whole.

## Findings

### Existing mathlib: useful mixed-exterior foundation already available

[ExteriorAlgebra/Product](https://github.com/leanprover-community/mathlib4/blob/1a547d8a48a8fa7877d2decb69d7294723bb0187/Mathlib/LinearAlgebra/ExteriorAlgebra/Product.lean)
provides `ExteriorAlgebra.prodEquivTensor`, an algebra equivalence from the
exterior algebra of a product module to the graded tensor product of its
exterior algebras. `prodEquivTensor_symm_apply_tmul_ιMulti` specifies the inverse
on pure wedges with concatenated included vectors. The graded tensor signs
are retained. Both declarations were checked in the project's environment;
the equivalence has only the three permitted standard axioms.

This strengthens the mixed-content route without adding a dependency.
It is not already the content-source theorem: one must extract the individual
species multidegree, iterate the binary equivalence, identify the repository's
statistical image, and prove equivariance for the actual action. The earlier
assessment should not be read as requiring a new exterior-algebra foundation.

### ATLAS: relevant names, but the v1 extraction candidates are incomplete

[ATLAS README](https://github.com/facebookresearch/atlas-lean/blob/8004bc185206d3d34cc6a7cf0840edca89cf64ce/README.md)
distinguishes its root development from the archived v1. Inspection of
[v1 KostantTheorem](https://github.com/facebookresearch/atlas-lean/blob/8004bc185206d3d34cc6a7cf0840edca89cf64ce/v1/Atlas/LieGroups/code/KostantTheorem.lean#L165)
found `KostantSetupData.weylCharacter_CT`, `weylCharacter_zero_eq` and
`weylCharacterFormula` with `by sorry` bodies. Later results using them cannot
supply a sorry-free extraction theorem. The character is also packaged in
setup data, so its identification with the actual SU3 source would need checking.
The v1 Peter-Weyl and Schur orthogonality files likewise contain unfinished
central statements. This finding is specific to inspected candidates, not a
claim that all ATLAS results are incomplete.

The root
[PeterWeyl](https://github.com/facebookresearch/atlas-lean/blob/8004bc185206d3d34cc6a7cf0840edca89cf64ce/MathlibExt/Topology/Algebra/PeterWeyl.lean)
contains a proof of `peter_weyl_point_separation`. That is point separation by
finite unitary representations, not Weyl integration over a maximal torus.
`MathlibExt/GroupTheory/IrreducibleCharacterBasis.lean` concerns finite-group
character bases; its finite-group endpoint does not cover SU3. Neither replaces
the missing A2 adapter. No external transitive axiom audit or port was attempted.

Licensing is another adoption input: the pinned root LICENSE carries Apache
text and an ML-use notice; v1/LICENSE retains CC BY-NC terms and an additional
ML-use restriction. The two source locations cannot be treated as having one
uniform license. No ATLAS code was copied into this repository.

### LeanPool: genuine divided-difference helpers, not an A2 theorem

[DemazureRelations](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DemazureOperatorsLean/DemazureRelations.lean)
proves square-zero, adjacent braid and distant commutation relations for
`DemazureLinear`. Inspection of `Demazure.lean` shows the operator is the
polynomial divided difference with numerator `p - SwapVariables ... p`.
It must not be confused with an already proved representation-theoretic
Demazure character formula. A Laurent/weight-lattice extension and the actual
representation-character bridge would still be required for that route.

The unmodified base `Demazure.lean` compiled against the current project pin.
This is a bounded positive compatibility result; the relations' full import
closure and transitive axiom audits have not been checked here. The file has
an Apache-2.0 header. Inspect the upstream project attribution before any port.
[RootSystem/An](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RootSystem/An.lean)
provides a concrete type-A reduced root pairing; it does not establish
representation multiplicities. These are optional helper candidates, not a
reason to import all LeanPool projects.

### Other candidates and existing TauCeti

[Physlib](https://github.com/leanprover-community/physlib/tree/c3964f48db4b861c8ebe706d8ff6febe07025827)
was screened through its complete file inventory and pinned configuration.
SM representations, Weyl spinors and continuous-representation files are
present. No directly matching A2 extraction candidate was identified in this
screen. This is an inventory/search result, not proof of absence or a theorem-
level review of every file.

The existing TauCeti `WeylModule/Character`, `SchurWeyl`, `Multiplicity` and
`SpecialLinear` APIs remain the closest representation-specific inputs:
Schur/power-sum character identities and special-linear restriction are
already at the project pin. Their combination still requires the actual
SU3 invariant/branching connection. The
[TauCeti highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
is a discovery aid, not an implemented theorem or imported premise.

## Recommended continuation

Start mixed contents with the existing mathlib product equivalence and
TauCeti exterior bases; freeze the multidegree and actual-action transport
as the first acceptance theorem. No new library is presently needed there.
For A2, first test the pinned TauCeti Schur-character/special-linear route
against the precise extraction statement. LeanPool divided differences are
an optional second algebraic route if their representation bridge can be
specified. The inspected ATLAS v1 formulas cannot be adopted as proved inputs.

Before adopting an external helper, compile its import closure against the
unchanged project pins, check its exact statement and actual-source adapter,
run the project's strict transitive axiom/layer audits, and preserve upstream
license/attribution. If dependency or toolchain changes become necessary,
record the concrete proposal for the user's approval. This assessment neither
proves nonexistence elsewhere nor declares A2 formalization infeasible.

## Verification

Public GitHub recursive inventories for ATLAS, LeanPool and Physlib were
non-truncated. A selected set of 210 files from ATLAS/LeanPool was downloaded
to temporary storage for source/configuration inspection. Search misses were
followed by inspection of the specific candidate declarations above.

Executed:

    lake build Mathlib.LinearAlgebra.ExteriorAlgebra.Product
    lake env lean /tmp/sm-exterior-product-probe.lean
    lake env lean /tmp/sm-library-review/lean-pool/LeanPool/DemazureOperatorsLean/Demazure.lean

The focused mathlib build passed (1863 jobs). The probe checked the two named
product declarations and printed standard axioms for `prodEquivTensor`.
The unmodified LeanPool base file compiled with no diagnostics. No project
proof source was changed; no full project `lake build` was rerun, and no new
formal theorem or external-package audit baseline is claimed. Documentation
links passed for 831 Markdown files, 5112 local links and 94 fragments;
`git diff --check` passed.
