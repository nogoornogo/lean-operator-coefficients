# Bounded Assessment Of Noncommuting SU(6) Protection

## Preserved Conditions And Desired Conclusion

The starting conditions are finite-dimensional continuous-unitary SU(6) matter,
an ordinary complex-linear Abelian candidate residual action, and the
[original mass/index conditions](../../proof/current/inputs/GUT/WEYL_MODEL.md).
The positive profile extension uses an exact dual radical-index target,
not an exact full light spectrum; see [profiles](../../proof/current/applications/GUT/PROFILE_MODEL.md).
Only strict commutation with the full UV SU(6) action is being relaxed.
Mass invariance must be interpreted at the broken phase, not strengthened to
full-SU(6) mass invariance. Quantum exactness remains an external input.

The desired finite endpoint is zero invariant dimension-six Delta-B-one
coefficient space on the actual light fields. It is not a physical proton
lifetime theorem. Neither an absent charge prohibition nor a nonzero internal
signature alone proves a nonzero full gauge/Lorentz/exterior coefficient.

## Route 1: Homomorphic Inner Gauge Lift

[GaugeTwistedAction](../../../GUT/SU6/SelectionRules/StandardBranch/FiniteResidualActionFactorization.lean)
requires an Abelian H, a unitary physical representation U, and a supplied
homomorphism s from H to SU(6), satisfying

```text
U(h) rho(g) = rho(s(h) g s(h)^(-1)) U(h).
E(h) = rho(s(h)^(-1)) U(h).
```

`externalRepresentation` constructs E as a representation;
`externalRepresentation_commutes` proves E commutes with all SU(6).
This is conditional on a homomorphic lift. No theorem here says every inner
covariance admits that lift; central cocycles and non-split extensions are
outside this inspected interface.

[StandardBlockGaugeCancellation](../../../GUT/SU6/SelectionRules/StandardBranch/StandardBlockGaugeCancellation.lean)
proves exact additive cancellation. With external charges k and color/weak
block charges C,W, its physical charges are

```text
Q = kQ + C + W       u = ku + 2C       e = ke + 2W
 d = kd - C          l = kl - W
2Q - u - e = 2kQ - ku - ke
Q + l - u - d = kQ + kl - ku - kd.
```

These are the source module's charge conventions; they are not substituted
into a different all-left or physical-right-handed dictionary.
The identities hold in arbitrary additive Abelian charge groups, so torsion
charges are included without choosing roots.

The source endpoint
`PureSMActualBlockGaugeSource.physical_protonCharacters_eq_one` additionally
requires a common lift centralizing the selected semisimple embedding, a
nonzero generation index, an exact coefficient-level SM target for the
external source, and an explicit identification of physical field charges.
Under those certificates both physical proton characters are trivial.

Those certificates are not inferred automatically from the original mass
radical index for every twisted model. The new task does not manufacture that
missing model adapter. Nevertheless, a candidate satisfying these certificates
cannot obtain protection merely from these block-gauge charge shifts.

## Route 2: General Automorphism Covariance

A proposed replacement is an action alpha of H by SU(6) automorphisms and

```text
U(h) rho(g) U(h)^(-1) = rho(alpha(h)(g)).
alpha(h k) = alpha(h) composed with alpha(k).
U(h k) = U(h) U(k).
```

For a specified scalar representation sigma and scalar action S, require the
same covariance there. A vacuum v must be fixed by the chosen physical
residual action (or by an explicitly defined compensated action). The effective
mass must be invariant under that action and the unbroken gauge group.
The action must preserve the light subspace and descend to the coefficient
space, including fermion exchange and Lorentz/gauge constraints.

For compensated transformations the group law must be checked again;
pointwise compensators do not automatically define a representation.
For the original positive chiral target, compatibility must be proved on the
actual light fields. A mere permutation of UV weights is insufficient.

There is no general automorphism-covariant physical model / coefficient adapter
in the inspected SU(6) sources. Searches for SU6/MulAut covariance and outer
routes were followed by inspection of the actual inner-lift structure above;
existing embedding conjugations do not supply this interface. No classification
or exclusion of outer actions is claimed by this search.

The existing completeness theorem assumes commuting local/residual actions.
It cannot be applied unchanged to U before descent or compensation. A new
bridge must either construct an eligible commuting action or prove the relevant
coefficient classification in the covariant setting.

## Decision And Next Finite Problem

No protecting mechanism has been derived. The inner-lift route is constrained
by existing cancellation; route 2 needs new model data and a theorem-level
interface. The bounded investigation ends here under the repository's stop gate.

A next task should select one explicit finite H and one explicit automorphism
action, state admissible SU(6) matter/scalars and the vacuum condition, and ask
whether a positive SM light target and complete dimension-six prohibition can
coexist. It must distinguish a proof of no solutions from a failed candidate.
A general classification of all noncommuting protecting actions is not the
next implicit obligation.

## Reproducing The Declaration Inspection

From the repository root, after compiling the existing imports, save the
following as a disposable Lean file and run `lake env lean <file>`:

```lean
import GUT.SU6.SelectionRules.StandardBranch.StandardBlockGaugeCancellation
#check GUT.FiniteResidualActionFactorization.GaugeTwistedAction
#check GUT.FiniteResidualActionFactorization.GaugeTwistedAction.externalRepresentation_commutes
#check GUT.StandardBlockGaugeCancellation.PureSMActualBlockGaugeSource
#check GUT.StandardBlockGaugeCancellation.PureSMActualBlockGaugeSource.physical_protonCharacters_eq_one
#print axioms GUT.FiniteResidualActionFactorization.GaugeTwistedAction.externalRepresentation_commutes
#print axioms GUT.StandardBlockGaugeCancellation.PureSMActualBlockGaugeSource.physical_protonCharacters_eq_one
```

This records a reproducible inspection, not a new strict audit module.
