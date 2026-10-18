# Mechanism Completion: Bounded Result

The reusable neutral-kernel and coefficient-restriction work is complete.
Selected finite PS Yukawa contractions are derived. Full admission of the
paper's PS representations remains open; this is not paper-wide verification.
See the [frozen plan](mechanism-completion-plan.md) and
[verification](mechanism-completion-verification.md).

## Arbitrary Copy Spaces

[Math.NeutralKernelGraph](../../../Math/LinearAlgebra/NeutralKernelGraph.lean)
works over any field and modules A,B,C, with D:A→B and invertible M:C→B.
For the block map (a,b,c)↦(Eb,Da+Mc,Nb), injectivity of N gives the entire
kernel as (a,0,−M⁻¹Da). E is unrestricted. Neither finite dimension nor
symmetry of this auxiliary block map is assumed.

[NeutralDiracGraph](../../../Physics/FieldTheory/Mass/NeutralDiracGraph.lean)
constructs the physical symmetric Weyl bilinear using the shared Dirac
convention. On (A×C)×B*, its radical is exactly
((a,−M⁻¹Da),0). The vanishing dual coordinate follows from surjectivity of
M, rather than an extra assumption on a reverse block. This includes arbitrary
copy spaces and mixing matrices of this form. Invertible heavy mixing and
absence of additional Majorana blocks remain hypotheses; it is not a theorem
for every invariant mass matrix or finite-mu spectrum.

For an alternating coefficient f of any arity, restriction is actual pullback
to this graph. The restricted coefficient vanishes if and only if f vanishes
on every tuple from the complete mass kernel. A nonzero restriction has an
explicit evaluation witness; invertible changes of graph coordinates preserve
nonzero. These results do not assert that arbitrary ambient nonzero f survives
restriction. They supply a reusable restriction interface, not an automatic
multi-generation matching theorem. Kinetic normalization and model-specific
Lorentz/SM/residual admission must still be supplied for each application.

## Selected PS Action

[SelectedPSYukawa](../../../GUT/PatiSalam/Matching/SelectedPSYukawa.lean)
defines the full finite color/weak-index Yukawa sums. It derives their selected
Phi, neutral chi and colored chi restrictions, including the same chi coupling
in neutral mass and colored vertex. Hermitian conjugation then connects these
sums to the existing source-action parameter map and Grassmann brackets.
The diagonal Phi vacuum and selected coupling slice remain inputs. The existing
one-generation normalized coefficient theorem continues to apply under its
explicit source, kinetic and UV-coefficient premises.

The pinned source is [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/html/2211.02054v2),
Eqs.(2),(6),(10)–(14),(19)–(24),
[PDF](https://arxiv.org/pdf/2211.02054v2),
[publication](https://doi.org/10.1103/PhysRevD.107.035019).

[MassNormCrosscheck](../../../GUT/PatiSalam/Matching/MassNormCrosscheck.lean)
rechecks the earlier sqrt(2) discrepancy using the sum of squared entries:
the displayed heavy-entry matrix weight minus the translated matrix weight is
2‖M‖². This is a second algebraic calculation within the same canonical
dictionary. It does not independently establish that dictionary's semantic
faithfulness to every paper convention, or prove unitary-congruence invariance.
No paper-error theorem is claimed.

## Remaining Admission And Stop

A complete PS application still needs explicit PS actions on the fermion and
scalar spaces, an SM embedding, component inclusions/projections intertwining
those actions, and proofs that the restricted Yukawa and UV epsilon actions
coincide with the typed coefficients used here. Vacuum and residual-action
compatibility must be checked alongside these maps. Finite index sums and
hypercharge arithmetic alone do not discharge this interface. The missing
representation adapter need not require a new global-quotient foundation,
but it is a separate proof obligation from the component identities completed
here. No such admission is silently assumed proved.

This is the frozen admission stop. No finite-mu approximation, rates,
hadronic cancellation claim, all-channel stability or ultraviolet origin of
C_X is established. The generic kernel result is reusable independently of PS;
its new restriction criterion does not itself guarantee coefficient generation.
