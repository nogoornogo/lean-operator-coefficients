# Model-Facing Lagrangian Input

Enter the **total density**, choose a factory, then ask a full-source or
selected-subspace question. Existing direct EOM and expression factories remain
available.

## Registered Models

```lean
import Physics.FieldTheory.Jets.RegisteredLagrangianModels

noncomputable section
def scalarModel (g : ℂ) := GUT.RegisteredLagrangianModels.quartic g
def higgsModel (a b : ℂ) := GUT.RegisteredLagrangianModels.higgs a b
```

`scalar g` selects the sixth-power potential; `quartic g` selects the quartic
potential. Both package actual scalar Lorentz action.
`higgs a b` includes checked global internal and Lorentz actions; use a=-m2,
b=lambda for the stated Warsaw convention. Their `.input` is the existing
generated input.

```lean
import Physics.FieldTheory.Jets.YukawaModel

noncomputable section
def mixedModel (massSquared m y : ℂ) :=
  GUT.YukawaModel.model Complex.I massSquared
    (fun c => if c then star m else -m)
    (fun c => if c then star y else -y)
```

This has scalar and Weyl kinetic terms, scalar/fermion masses and a Yukawa
interaction. Four odd components form the two chiral/conjugate pairs; the
existing even carrier uses one scalar and three unused spectators. All
couplings may vanish. The parameter dictionary is proved against the selected
[DHM formulas](literature-validation.md). Conjugate labels are independent
complexified generators, not a reality quotient.

## Shared Operations

Both `Math.LagrangianModel.Bosonic` and `.Mixed` expose:

| Operation | Result |
| --- | --- |
| `M.input` | Existing `DerivativeInterface.Input` |
| `M.presentation`, `M.Coordinates` | Complete all-order relation/group equations and their solutions |
| `M.equivalence` | Inverse coefficient/coordinate maps |
| `M.evaluate q u` | Reconstructed coefficient on an actual source expression |
| `M.evaluate_encode`, `M.reconstruction` | Evaluation preservation and finite-sum reconstruction |
| `M.prescribed_iff`, `M.target_values_iff` | Necessary and sufficient monomial or chosen target values |
| `M.forbidden_iff`, `M.allowed_iff` | Existing prohibition/allowance predicates |
| `M.selected V hV` | Input retaining the full relation preimage in invariant V |
| `M.selectedPresentation V hV`, `M.selectedEquivalence V hV` | Selected coordinates and inverse maps without a global-extension hypothesis |

For selected target values, use
`(M.selectedPresentation V hV).target_values_iff targets values`. A preferred
basis can instead be supplied through
`M.presentation.selectedPresentation V hV basis`. Default selected bases
are chosen noncomputably. High-degree relations may combine to affect V.

The complete quartic example proves
`(∃ q, (quartic g).evaluate q (field^3) = c) ↔ g*c = 0`.
Value one is admitted at g=0 and forbidden at g=1. General models expose exact
equations; these need not have an automatically computed finite solution or count.

## A New Density Or Interaction

Without a requested group, use `LagrangianModel.Bosonic.trivial L` or
`LagrangianModel.Mixed.trivial L`. With a checked full-relation stability
proof, construct the record from L, rho and that proof.

`Bosonic.ofEulerSpan` and `Mixed.ofEulerSpan` offer a smaller certificate:
the action preserves multiplication, derivatives transform by a supplied finite
matrix, and every transformed Euler component belongs to the span of the total
Euler family. The factory proves stability of **all** differential descendants,
left/right products and linear IBP. This route requires a finite direction
type; the model record itself does not.

The [successor input](../euler-naturality/input-guide.md) derives the Euler
certificate from evaluated density invariance for constant linear field and
direction representations. The Yukawa model agrees with this automatic
constructor. Other actions can retain the Euler-span certificate; each added
interaction must satisfy the chosen input conditions.

Generate EOM after adding all terms. Separate equation ideals can retain terms
that cancel in the total density. Interactions also require rechecking the
applicability of earlier free-input dimensions and completeness results.
