# Compact Residual Symmetry On Actual QQue Light Fields

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Statement

[CompactLightQque](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/CompactLightQque.lean)
extends the four-weight non-Abelian qque source endpoint to compact topological
groups H with continuous residual action. H need not be finite or Abelian.

Keep the two actual ambient conjugations, finite-dimensional complex source,
T-unitarity, T x H-invariant symmetric bilinear mass, and the local H-character
target at weights 0, 3, 8, 14. Assume joint continuity of the residual H action
on the source and of the nonzero finite-dimensional Q target. No topology on
G or continuity of the conjugators is required.

Then the ordered tensor product of actual light sectors has a nonzero
H-equivariant linear functional:

```text
Hom_H((Q_0 tensor Q_3) tensor (u_8* tensor e_14*), C) != 0.
```

These are the same mass-radical weight spaces and algebraic contragredients
used in the finite theorem. Consequently complete exclusion of both internal
qque and duql coefficient spaces is impossible, using qque alone. No duql
existence theorem for compact infinite H is asserted by this result.

## 4. Proof structure

### Proof Connections

1. [ContinuousDual](../../../../../Math/RepresentationTheory/Unitary/ContinuousDual.lean)
   equips the existing algebraic dual locally with the pulled-back continuous
   dual norm, preserving its addition, scalar multiplication and action. Its
   contragredient is jointly continuous by evaluation at rho(h^-1)v.
2. [CompactIrreducibleQuotient](../../../../../Math/RepresentationTheory/Decomposition/CompactIrreducibleQuotient.lean)
   uses a finite Hilbert copy and TauCeti unitarization, then transports
   semisimplicity back to the original representation as a group-algebra
   module. The mass and light subspaces are not transported or replaced.
3. [CompactPositiveCharacterQuotient](../../../../../Math/RepresentationTheory/Characters/CompactPositiveCharacterQuotient.lean)
   uses the audited Haar character/Hom-dimension formula. A positive actual
   target constituent yields a surjection from the actual light sector.
4. [ResidualWeightContinuity](../../../../../Math/RepresentationTheory/Characters/ResidualWeightContinuity.lean)
   descends residual continuity to invariant subspaces and torus weights.
5. [CompactResidualLightQuotient](../../../../../Physics/FieldTheory/Mass/Algebra/CompactResidualLightQuotient.lean)
   combines the target, the actual opposite-weight dual, and semisimple
   splitting to derive one nonzero irreducible split quotient common to the
   four sectors.
6. The existing ordered evaluation-pairing construction yields the nonzero
   functional. Conjugation/dual-index transport is unchanged.

### Explicit SM Extension

The [SM x H tensor adapter](EXPLICIT_SM_RESIDUAL_TENSOR.md) consumes this
theorem without changing its hypotheses. With **additional** compatible
full-SM field decompositions on the radical and its dual, it yields a nonzero
ordered SM x H invariant qque functional on those actual subrepresentations.
These decompositions are not consequences of the four-weight target. The
arbitrary-radical boundary above remains in force. The subsequent
[spinor/exterior theorem](LORENTZ_EXTERIOR_QQUE.md) also closes algebraic
fermionic nonvanishing under the explicit adapter inputs, not from torus-only
data and not as a statement about generated interactions.

## 5. Lean entry points

### Exact Interface

- `rho : Representation C (G x H) E` encodes strict commutation.
- Only its torus restriction must preserve the supplied inner product.
- `SymmetricMass` is unchanged; invariance is under T x H, not all of G.
- `TwoConjugations j` and `FourWeightLightQque.HasTarget` are unchanged.
- `IsJointlyContinuous (rho.comp (MonoidHom.inr G H))` supplies residual
  continuity. Continuity on the radical and its weight spaces is derived.
- The five target carriers are complex normed spaces; only P_Q is required
  finite-dimensional, nonzero and jointly continuous by this endpoint.
  There are no new continuity assumptions on P_up or P_e, whose characters
  are forced equal to P_Q. Down/lepton matching remains unused. The usual
  finite-dimensional target families fit this interface.
- A Borel structure for H is chosen internally for integration; it is not
  an additional parameter at the physical endpoint.

No H-unitarity, invariant inner product, common irreducible constituent or
split light projection is assumed. Continuity is essential to the compact
argument; this does not cover arbitrary discontinuous representations of an
infinite abstract group.

## 6. Scope and limitations

### Compatibility And Boundary

The original finite theorem remains available without any topology or norm
on its target carriers. A finite/discrete control verifies the compact route
on normed finite-dimensional targets: both continuity premises follow
automatically. The conclusion is the same existential nonzero functional,
not equality of the chosen witnesses.

This is an ordinary residual internal-symmetry statement, not quantum anomaly
consistency, full SM-gauge invariance on arbitrary radicals, Lorentz/Grassmann
nonvanishing, generated Wilson coefficients, an amplitude or a proton lifetime.
The Abelian endpoints, finite pair theorem and E6 literature boundary are
unchanged. No additional embedding class or realistic model is exhibited.

Verification and integration: [topic record](../../../../topics/compact-light-qque/README.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
