# Signed Virtual Indices: Checked Result

## Statement

[VirtualIndexQque](../../../Physics/StandardModel/Operators/VirtualIndexQque.lean)
replaces the positive actual residual target in the species-index route with
a finite signed virtual character of positive total dimension. The conclusion
is unchanged: participating actual light fields admit a qque coefficient with
nonzero alternating descent, and hence a nonzero invariant functional on their
fourth exterior power with the existing left/right spinors.

The normalized input is a finite family of pairwise inequivalent continuous
irreducible complex H representations S_i, with finite-dimensional normed
carriers V_i. Integer coefficients a_s(i) describe each species index:

```text
chi_s(h) = sum_i a_s(i) chi(S_i)(h)
dim(chi_Q) = sum_i a_Q(i) dim(V_i) > 0.
```

Coefficients may be negative. The same actual compact-continuous H,
finite-dimensional ambient source, symmetric invariant mass and unchanged
radical K are used. The continuous compatible SM-cover x H action on K remains
an input. The new endpoint does not assume a common quotient or coefficient.

There are two entry points:

- `exists_actual_alternation_of_common_index` takes the three actual
  SM-species dual-index equations and equality of their virtual characters.
  It does not use a separate four-weight/conjugation premise.
- `exists_actual_alternation` and `exists_actual_exterior` derive those
  equalities from two actual ambient conjugations, T-unitarity and the
  retained four-weight matching condition at 0, 3, 8, 14. Species-index
  matching uses the same signed profiles. No down/lepton matching is imposed.

The endpoint is under SM-cover x H x SL(2,C). It concerns an allowed algebraic
coefficient, not a generated Wilson coefficient, decay amplitude or lifetime.

## Proof

1. [Virtual character pairing](../../../Math/RepresentationTheory/Characters/CompactVirtualCharacter.lean)
   recovers each integer coefficient by compact character orthogonality.
   Positive total dimension supplies an i with a_Q(i) > 0.
2. If chi(L) - chi(N) = chi_Q, pairing with S_i proves
   dim Hom_H(L,S_i) - dim Hom_H(N,S_i) = a_Q(i). Thus L maps nontrivially
   onto S_i; irreducibility gives surjectivity and compact semisimplicity gives
   a split. Neither L nor N is assumed to be supplied in irreducible coordinates.
3. [Multiplicity extraction](../../../Math/RepresentationTheory/Multiplicity/CompactVirtualMultiplicityIndex.lean)
   applies this to the actual species index
   Hom_SM(R,K) minus the dual of Hom_SM(R.dual,K).
4. [Species compatibility](../../../Physics/StandardModel/Spectrum/VirtualSMSpeciesIndex.lean)
   uses conserved mass dual indices and actual conjugation to relate the Q,
   up and electron signed characters. All three actual multiplicity spaces
   therefore have a split onto the same nonzero S_i.
5. The existing SM field extraction and spinor/exterior theorem provide the
   actual subspaces of K and K.dual and nonzero alternating descent. The same
   Q projection is used twice; no additional generation or exchange premise
   is introduced.

## Signed Control And Boundaries

The [persistent mathematical audit](../../../Math/RepresentationTheory/Characters/Audit/AuditCompactVirtualCharacter.lean)
uses H = Circle and chi(z) = 2 - z. It proves dimension 1, a genuinely negative
coefficient, realization as a difference of actual continuous representations,
and extraction of an actual trivial-line split quotient. It also proves that
this virtual character is **not** the character of any finite-dimensional
continuous actual H representation. This witnesses a genuine distinction
from a positive actual target at the extraction level, not a newly constructed
GUT model with that index. Zero and negative total-dimension controls prevent
mistaking the positivity premise for an automatic property of signed data.
They do not assert absence of invariant coefficients at nonpositive dimension.

Normalization matters: coefficients of repeated isomorphic irreducibles can
cancel. Pairwise inequivalence ensures that pairing extracts the stated
coefficient, rather than a sum over equivalent labels. `character_injective`
also proves uniqueness of coefficients in a fixed normalized family.

**The API still requires the normalized finite virtual presentation.** This
task does not construct it automatically from an arbitrary pair of actual
representations. If an actual nonzero target has such a presentation,
`dimension_pos_of_actual` discharges positivity and `nonnegative_of_actual`
proves its coefficients are nonnegative. These are recovery lemmas, not an
automatic conversion of every old endpoint's inputs to the new API. Existing
positive-target and exact-spectrum theorems are unchanged.

Equal particle counts or equal index dimensions alone are insufficient: the
equations are for every h in H. Neither absence of extra fields nor exact SM
particle content is imposed, but additional fields must respect both index
packages. No new physical model, anomaly consistency, E6 identification or
larger embedding class is claimed. The compactness and continuity requirements
are not weakened here.

## Verification

The mathematical and physical audits check 20 and 7 declarations transitively,
allowing only `propext`, `Classical.choice`, `Quot.sound`. Both also enforce the
source-layer import boundary. The computational qque test is an independent
finite one-generation cross-check, not a proof oracle or an end-to-end signed
GUT benchmark. Commands and integration status are recorded in the
[topic overview](README.md).
