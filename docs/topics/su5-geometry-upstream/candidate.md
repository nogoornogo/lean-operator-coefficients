# SU(5) geometry contribution candidate

Status: candidate and extraction boundary identified, stage 01.
**Not ported, not submitted, and not validated against a Physlib checkout.**
The local SU5-5 milestone requires identification only. Follow the
[separate fork/worktree workflow](../../architecture/UPSTREAMING.md); keep this repository's
dependencies pinned.

## Smallest Contribution

Start with the actual SU(5) group and the standard covering homomorphism,
including matrix unitarity, determinant one, and multiplication. Do not
submit the entire proton selection-rule development in the first PR.

The retrieved [Georgi-Glashow source](https://github.com/leanprover-community/physlib/blob/master/Physlib/Particles/BeyondTheStandardModel/GeorgiGlashow/Basic.lean)
still presents the group, inclusion, its kernel, and the induced quotient
embedding as informal entries. Its specified matrix order is weak-first,
whereas our implementation is color-first. This is a candidate based on
the inspected public source, not a claim about a pinned future target
revision or guaranteed acceptance.

The retrieved [SM source](https://github.com/leanprover-community/physlib/blob/master/Physlib/Particles/StandardModel/Basic.lean)
already supplies actual SM group/quotient infrastructure and the central
sixth-root subgroup. Reuse that API instead of reproducing it. Exact kernel
equality and the induced injective map make a coherent second contribution.

## Extraction Manifest

| Proposed slice | Local proof material | Porting obligation |
| --- | --- | --- |
| Group and covering map | `Embeddings/StandardModel.lean`: `circle_smul_unitary`, `rawMatrix_unitary`, `rawMatrix_det`, `rawHom`, `matrixHom`, `hom` | Use Physlib's SM group accessors and reconcile its U(1) carrier; put the weak block first or prove the reindexing equivalence |
| Exact kernel | `Embeddings/StandardModelKernel.lean`: scalar-block equations and `mem_ker_iff` | Identify with the existing target sixth-root subgroup, not merely an abstract isomorphic cyclic group |
| Injective quotient map | `Embeddings/StandardModelQuotient.lean`: `quotientHom`, injectivity | Use the target quotient after proving subgroup equality |
| Optional later topology | `continuous_hom`, closed quotient/image equivalence | Audit the target topology API; do not add all TauCeti for an algebraic first PR |

These paths are under `GUT/SU5`. The algebraic first slice needs no actual
matter, Schur decomposition, character-sector theorem, ordered proton tensor,
or SU(6) import. Its current local file imports more infrastructure for
shared types/topology: **extract declarations, not the whole import closure**.

## Future Port Gate

1. Pin the target revision and recheck whether the informal entries remain.
   Agree the small scope with maintainers before expanding it.
2. Use a separate fork/clone or a worktree of that fork, with its own
   toolchain, cache, and CI. Do not update this proof baseline for the port.
3. Match the weak/color order and phases exactly. Keep a nonidentity kernel
   witness and an uncompensated nonkernel control when porting the kernel.
4. Preserve copyright/attribution, confirm licensing and contributor names,
   disclose AI assistance, and recheck the current review/AI policy. No
   AI-only acceptance permission is inferred from the generic contribution
   page. Public submission requires a separate user decision.
5. Run the target's build and lint checks. Physlib's
   [contribution guide](https://physlib.io/getting-started#making-a-pull-request)
   recommends small PRs and describes the fork workflow. A locally
   kernel-checked result is not a claim that the port already builds there.
6. Retain the local theorem until an upstream release at a compatible
   revision can replace it in a separately audited dependency change.

General multiplicity/character results remain possible mathematical-library
candidates, but they are not dependencies to introduce in this first geometry
contribution. No upstream outcome is required for the local selection rule.
