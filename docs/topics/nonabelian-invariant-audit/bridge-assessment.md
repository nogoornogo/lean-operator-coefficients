# Light-Spectrum Bridge Assessment

## Decision

The bounded audit supports a specific finite-group proof route. It does NOT
prove a non-Abelian extension of the physical selection-rule theorem. No
assumption-respecting physical counterexample was constructed or excluded.
The two finite controls and this explicit closed/open interface inventory meet
the agreed audit stop gate. Do not continue into a new source-spectrum project
by appending more helper lemmas to this topic.

## Checked Interfaces

1. Actual ambient conjugation implies invariance of the radical dual-character
   difference, evaluated at every residual-group element. This uses arbitrary
   groups and does not assume that the conjugator preserves the mass radical.
2. For finite H in characteristic zero, `hom_finrank_add` turns an actual
   character equality `chi(L) = chi(S) + chi(P)` into additivity of dimensions
   of equivariant maps to any finite-dimensional test representation R.
3. If R is irreducible and there is a nonzero equivariant map P -> R, then
   `exists_surjective_of_character_add_of_nonzero` constructs an equivariant
   surjection L -> R. In particular, over an algebraically closed field,
   `chi(L) = chi(S) + chi(R)` produces such a surjection. S and P must be actual
   representations, not arbitrary virtual characters; this is the positivity
   condition that prevents a vacuous conclusion.
4. Four equivariant surjections onto V, V*, W, W*, with V,W nonzero, produce a
   nonzero invariant coefficient on the original four spaces. The witness
   evaluates to one. The four spaces may have additional constituents.
5. If the first map is zero, the pulled coefficient is zero. Mere equivariance
   cannot replace the surjectivity/nondegeneracy input.

Sources:

- [Actual mass/conjugation](../../../Physics/FieldTheory/Mass/ConjugationMassIndex.lean)
- [Positive character quotients](../../../Math/RepresentationTheory/Characters/PositiveCharacterQuotient.lean)
- [Nonzero pullback](../../../Math/RepresentationTheory/InvariantPairingTransport.lean)
- [Finite controls and coverage](finite-controls.md)

The quotient proof uses mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` and
`Representation.IsIrreducible.surjective_or_eq_zero` directly. It does not
assume an unproved equivalence between equal characters, and does not require
developing a new classification of finite-group representations.

## Remaining Inputs For A Subsequent Proof

### Weightwise Residual Modules

For the actual T x H action, construct the torus-weight spaces of the radical
as H representations. Commutation should imply their stability under H; it
does not imply that H acts by scalars. Prove the dual/opposite-weight relation
and the finite character expansion, then extract the coefficient identities
from the already checked full dual-character conjugation identity. The
existing Abelian joint eigenbasis over T x H must NOT be used unchanged.

### Positive Local Target And Common Constituents

A candidate replacement for scalar charge profiles is: at each monitored
oriented SM weight w, a finite-dimensional positive H representation P_w
satisfies

```
chi(light at w) = chi(dual of light at -w) + chi(P_w).
```

This equation is a PROPOSED non-Abelian light-target interface, not a theorem
about every mass sector and not yet a formal definition in this project.
On Abelian H it must be checked against the existing coefficientwise target,
not justified merely by matching dimensions. Q/down positivity should mean
nonzero target representations, without requiring equal dimensions.

Do not assume P_Q = P_u = P_e or P_d = P_L. Derive their character relations
from the actual conjugations, select a common irreducible constituent, and
use the checked quotient lemmas to obtain the needed maps on the actual light
spaces. Existing semisimple/isotypic infrastructure is a candidate for the
selection step; its concrete application and the dual bookkeeping remain
unproved. No isomorphism of entire light spaces is needed.

### Physical Ordering And Endpoint

Transport the four maps and the coefficient to the qque/duql factor order.
For example, the pairing order Q, u*, Q, e* differs from Q, Q, u*, e* by
the standard tensor symmetry; labels must be tied to actual SM fields.
Connect the resulting coefficient to the appropriate replacement for the
current scalar-charge support predicate. A raw internal invariant does not
establish nonzero Lorentz/Grassmann contraction or a generated interaction.

## Recommended Next Bounded Task

After approval, open a separate source-bridge topic. Its acceptance conditions
should be the weightwise H-module construction, the local-target contract and
Abelian recovery, and a theorem producing matched light quotients and ordered
invariant coefficients from those inputs. If one of these needs new foundations
outside existing finite-dimensional representation theory, stop and report it.

Do not reopen non-SU5 embeddings, SU(2)/SU(3) flavor classification, anomalies,
E6 topology, vacuum dynamics, or nonzero decay amplitudes as prerequisites.
