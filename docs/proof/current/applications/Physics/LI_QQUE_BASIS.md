# Normalized Li D.38 Qque Basis Certificate

## Result

A literal local-contraction interpretation of Li et al., arXiv:2201.04639v2,
appendix D.1 equation (D.38), presents the independently defined derivative-free
qque exterior coefficient sector. The result proves semantic contraction
agreement and two-sided coordinate reconstruction, not merely a dimension count.

Sources:
[`LiQqueConvention`](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/LiQqueConvention.lean),
[`LiQqueCoordinates`](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/LiQqueCoordinates.lean),
[`QqueResidualHom`](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/QqueResidualHom.lean).
Strict checks:
[`AuditLiQqueBasis`](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/Audit/AuditLiQqueBasis.lean).

## Published Data And Explicit Dictionary

The [PDF, page 52](https://arxiv.org/pdf/2201.04639v2#page=52) prints

```text
Q_1 Q_2 e_C†_3 u_C†_4:
C^[2]_(f1 f2, f3, f4) ε^(a1 a2 a4) ε^(i1 i2) ⟨12⟩[34].
```

The repeated Q flavors are symmetric (`[2]`). The paper is a source of this
expression, not a trusted completeness axiom. The theorem interprets the two
brackets as the repository's normalized alternating pairings in independently
chosen left/right spinor bases; both evaluate to 1 on their ordered standard
basis pair. The color and weak epsilons are determinant pairings normalized in
the same way. This explicitly fixes the local coordinate convention. No physical
external-state/LSZ normalization is asserted.

For arbitrary complex H representations `a,b,d` on `A,B,D`, the undaggered
singlet gauge/flavor dictionary is `upRight.dual tensor b` and
`electronRight.dual tensor d`; daggered fields use the gauge double dual and
`b.dual`, `d.dual`, with right Weyl spin. `ucDaggerEquiv` and `ecDaggerEquiv`
construct the canonical bidual gauge identifications. They do not assume a
Hermitian structure on the arbitrary residual representations. This is an
algebraic contragredient field convention: a physical model interpreting dagger
as conjugation must supply its identification with this dictionary. An arbitrary
physical field assignment is not inferred from matching labels or flavor counts.

## Semantic Proof

`paperOrdered_apply` proves exactly the printed epsilon/bracket product in
`Q,Q,E,U` order. `fermionic_reorder` proves that its pullback to `Q,Q,U,E`,
including the odd fermionic transposition, equals the existing ordered
coefficient. The minus from reversing the right bracket cancels the Fermi minus.

`candidate` takes this actual ordered contraction through alternating descent
into the independent species-scaling sector. `candidate_eq` proves agreement
with existing assembly. `candidate_probe` retains the factor 2 of raw
alternatization on symmetric Q residual inputs; it is not silently normalized
away. With finite-dimensional `B,D`, `equiv` proves this candidate family
exhaustive using existing gauge/spinor uniqueness and qque completeness.
`onDaggerFieldsEquiv` transports the classification through the constructed
bidual dictionary; `onDaggerFields_candidate` proves that this also transports
the actual candidate coefficient. No compactness, continuity, mass or nonzero
premise is used.

## Finite Flavor Coordinates And Inverses

Supply finite bases of `A,B,D`, indexed by `I,J,K`. The coordinate matrix has
rows `J × K` (U then E), columns `Sym I 2` (unordered Q pairs). The paper's
flavor order is Q,Q,E,U: its last two flavor indices therefore correspond to
E and U, respectively. Matrix rows intentionally follow repository order.

`matrixEquiv` reuses the pinned symmetric-power, tensor-product and matrix
coordinate equivalences. `homEquiv_entry` evaluates an unordered Q pair;
`residual_entry` and `QqueResidualHom.equiv_symm_tprod` prove that its entries
are evaluations against the U and E dual bases. Operator inputs and
coefficient duality are thus explicitly related, not silently identified.

For arbitrary H, `mem_matrixSpace_iff` gives exactly

```text
M A_Sym²(h) = A_(B tensor D)(h) M   for every h.
```

`sectorEquiv`, `inverse_left`, `inverse_right` and `inverse_is_candidate`
check the two-sided coordinate certificate on this constrained space. General
matrix units need not be invariant; no independent-input result is transferred
to an arbitrary residual action.

For trivial residual action, every matrix is admissible. `flavorEquiv` checks
both inverses on unrestricted matrices. `flavorBasis` is the finite matrix-unit
family transported into the actual exterior sector; `flavorBasis_is_candidate`
identifies every member with the mapped paper contraction.
`flavor_paperOrdered_apply` proves the literal D.38 formula for arbitrary flavor
matrices. `flavorBasis_independent` and `flavorBasis_spans` certify the entire
family. For equal flavor number n its size is n² * multichoose(n,2); the audit
checks n=3 gives 54, n=1 gives 1, and an empty singlet flavor space gives 0.

## Scope And Verification

Appendix D explicitly distinguishes its amplitude bases from earlier operator
bases. The checked result is the stated derivative-free local contraction
interpretation. It neither executes ABC4EFT nor certifies its exact runtime
p-basis arrays, the full paper, general amplitude/operator correspondence,
derivatives, EOM/IBP, physical matching or rates.

The [topic verification record](../../../../topics/li-basis-verification/README.md)
records focused/full builds, strict transitive axiom/import audit, source layout,
Markdown links and exact component cross-checks. The new
[Li sign test](../../../../../tools/qque/audit_li_d38.py) independently expands the
normalized paper contraction in the one-generation Grassmann algebra. Omitting
the Fermi sign is a negative control. These finite computations supplement the
Lean proofs and are not premises of them.
