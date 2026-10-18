# Standard SU(5) embedding and quotient

## 1. Result And Status

Declaration map for the established interfaces below. The standard covering
homomorphism has central cyclic kernel of order six and a closed quotient
embedding into SU(5).

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Status: `LEAN-CHECKED`, SU5-2, stage 01.

## 2. Inputs And Conclusion

The covering group is `SU(3) x SU(2) x Circle`, with the fixed color-first `3+2` block order.

### Scope

The actual covering group is `StandardSMGaugeTensor.GaugeGroup`, namely
`SU(3) x SU(2) x Circle`, and the target is the compact matrix group SU(5).
The continuous homomorphism is

```text
hom (A,B,z) = diag(z^(-2) A, z^3 B).
ker hom = { (z^2 I_3, z^(-3) I_2, z) : z in Circle, z^6 = 1 }.
ker hom is central and isomorphic to Multiplicative (ZMod 6).
(SU(3) x SU(2) x Circle) / ker hom is topologically group-isomorphic to range hom.
```

The quotient map into SU(5) is a closed topological embedding. The covering
map is not injective. These statements are geometry, not a classification
of all embeddings, an exact vacuum-stabilizer theorem, or an SU(5) proton
selection-rule endpoint. No matter representation or residual action is
assumed or classified in this milestone.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Block equations compute the kernel; roots of unity identify the cyclic group and
the topological first isomorphism theorem identifies the quotient image.

### Proof Inputs

1. Block-matrix multiplication, unitarity, and determinant computations
   establish the actual map. The exponents obey `(-2)*3 + 3*2 = 0`.
2. A matrix in the kernel has both diagonal blocks equal to the identity.
   Solving these equations gives the scalar factors. The SU(3) determinant
   condition then forces `z^6 = 1`. Conversely every such root constructs
   actual SU(3)/SU(2) factors and an element of the kernel.
3. The pinned mathlib `ZMod.rootsOfUnityAddChar` and its bijectivity theorem
   identify these roots with the cyclic group; no root-classification
   hypothesis is assumed.
4. The pinned TauCeti special-unitary compactness instances, continuity,
   and the Hausdorff matrix target make `hom` a closed, hence strict, map.
   Mathlib's `ContinuousMulEquiv.quotientKerEquivRange` gives both directions
   of continuity for the first isomorphism theorem.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declaration Map

All declarations below are in `GUT.SU5.StandardModelEmbedding`.

| Module | Main declarations and responsibility |
| --- | --- |
| [StandardModel](../../../../../../GUT/SU5/Embeddings/StandardModel.lean) | `rawMatrix_unitary`, `rawMatrix_det`, `hom`, `continuousHom`; actual color-first `3 + 2` matrix homomorphism |
| Same | `hom_color_entry`, `hom_weak_entry`, `hom_cross_entries`; coordinate order and exact compatibility with existing `phase (-2)` and `phase 3` |
| [StandardModelKernel](../../../../../../GUT/SU5/Embeddings/StandardModelKernel.lean) | `hom_eq_one_iff`, `mem_ker_iff`, `kernelElement`; necessity and sufficiency of the complete kernel formula |
| Same | `kernelRootsEquiv`, `kernelCyclicEquiv`, `kernel_card`, `kernel_isCyclic`, `kernel_le_center`; roots-of-unity, cyclicity, cardinality six, and centrality |
| Same | `signKernelElement`, `hom_not_injective`; explicit covering-map collision |
| [StandardModelQuotient](../../../../../../GUT/SU5/Embeddings/StandardModelQuotient.lean) | `SMQuotient`, `quotientHom`, `quotientHom_injective`, `quotientHom_isClosedEmbedding`; the faithful quotient map |
| Same | `quotientImageEquiv`, `quotientImageEquiv_mk`, `image_isClosed`; topological group equivalence to the closed image, agreeing with the actual map |

The quotient has the standard quotient topology, not a transported or
discrete topology chosen to make continuity trivial. Compactness is
inherited from the covering group; Hausdorffness follows from the proved
embedding into SU(5).

## 6. Scope And Limitations

The covering map is not injective; no classification of all embeddings or exact
vacuum stabilizers is inferred.

## 7. Sources And Verification

The [scope dossier](../SM_BRANCHING.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Persistent Audit

[AuditStandardModelEmbedding](../../../../../../GUT/SU5/Audit/AuditStandardModelEmbedding.lean)
is imported by the root build. It checks:

- Color entries start at coordinate 0, weak entries at coordinate 3, with
  the existing integral-hypercharge phases.
- `(I_3, -I_2, -1)` is a nonidentity kernel element and becomes the identity
  in the quotient.
- `(I_3, I_2, -1)` is not in the kernel and survives the quotient. Omitting
  the compensating weak-center factor must not pass the test.
- The kernel is cyclic of cardinality six; the quotient is a compact
  Hausdorff topological group; its map is injective and the inverse of the
  image equivalence is continuous.
- A compile-time check rejects any transitive `GUT.SU6` module import.

Verification commands:

```sh
lake build GUT.SU5.Audit.AuditStandardModelEmbedding
lake build
```

Targeted audit: 3512 jobs. Full regression: 4271 jobs. Audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`
or native-decision axiom. Toolchain and dependency pins are unchanged.
