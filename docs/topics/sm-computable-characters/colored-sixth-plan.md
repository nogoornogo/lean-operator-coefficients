# Sixth-degree source comparison and assembly

Resume base `checkpoint 01`, branch `proof/sm-computable-characters`, integration
target `master`; no merge or push. This is the next bounded step of the
[completion plan](colored-support-completion-plan.md), after the
[complete fifth-degree result](colored-fifth-assembly-results.md).

## Frozen statement

For the actual gauge factor A=C tensor weak doublet, prove the complete
sixth exterior equivalence on independent-spin doublet external A. Write E
for trace-free color endomorphisms and H22 for the actual symmetric-square
partial-trace kernel. Proposed retained summands, all still proof obligations:

| Independent spin degree | Retained color/weak factors (color, weak degree) |
|---|---|
| 6 | (scalar,0) |
| 4 | (scalar,2), (E,2), (E,0) |
| 2 | (scalar,4), (E,4), (E,2), (E,2), (scalar,0), (E,0), (Sym^3 C,2), (Sym^3 C*,2), (H22,0) |
| 0 | (scalar,6), (scalar,2), (E,4), (E,2), (Sym^3 C,0), (Sym^3 C*,0), (H22,2) |

No numerical dimensions or multiplicities are asserted by this list. Each
row is an actual proposed representation, including two separate E weak-2
factors at spin degree 2. No irreducibility premise is added for E or H22.

## Interfaces and proof sequence

1. Identify exterior products at weights 6,4,2,0 with actual retained sums,
   using the already proved gauge exterior branches, adjoint product,
   symmetric-square/dual-square partial trace, and weak Clebsch-Gordan.
2. Construct actual consecutive-slice equivalences `Wk = Bk + W(k+2)`.
   At the top, the absent weight 8 is proved zero. Odd weights vanish by
   the uniform exterior parity theorem.
3. Apply `SU2IsotypicIdentify` to identify whole multiplicity modules;
   remove the absent odd-spin factors and assemble the complete source.
4. Transport to the established color/weak/spin factor order and actual
   Physics Q-core input. Conjugate transport remains an actual-source proof
   obligation, not a silently supplied comparison.

Product rearrangements may be generated as explicit coordinate projections
and inverse tuples; Lean must prove both inverse equations and equivariance.
Such generation does not evaluate dimensions, ranks or character coefficients.

The endpoint of this substep is the actual source equivalence and its strict
audit/full-build verification. A checkpoint continues to the conjugate and
general compatible positive color-coupling obligations. No new dependency,
literature premise, numerical certificate or proof-limit increase is allowed.

The source endpoint is now proved; see [results](colored-sixth-results.md)
and [verification](colored-sixth-verification.md). This remains a checkpoint
toward the general compatible color-coupling and full q/l endpoint.
