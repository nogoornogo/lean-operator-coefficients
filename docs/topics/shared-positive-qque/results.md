# One Shared Positive Constituent

## Checked Endpoint

[SharedPositiveQque](../../../Physics/StandardModel/Operators/SharedPositiveQque.lean)
proves `exists_actual_alternation` and `exists_actual_exterior` from one
shared positive irreducible coefficient in the three actual species indices.
The conclusion is the existing actual-field qque coefficient with nonzero
fermionic alternating descent and an invariant fourth-exterior-power
functional under SM-cover x H x SL(2,C).

Write each species virtual index in a supplied finite normalized family:

```text
I_s(h) = sum_i a_s(i) chi(S_i)(h).
SharedPositive a := exists i, a_Q(i) > 0 and a_up(i) > 0 and a_electron(i) > 0.
```

The three positive coefficients need not have the same value. All other
coefficients may differ and may be negative. There is no requirement that
the total dimension of any of these indices be positive or that their
whole characters agree.

## Inputs Kept And Outputs Derived

- H is compact, with a jointly continuous compatible SM-cover x H action
  D on the unchanged mass radical K. The existing finite-dimensional ambient
  representation and symmetric T x H mass are retained as the source carrier
  interface. No whole-radical field decomposition is supplied.
- S_i are pairwise inequivalent, continuous, irreducible finite-dimensional
  complex H representations on normed carriers. Automatic construction of
  this normalized presentation remains outside the task.
- `VirtualSMSpeciesIndex.SpeciesMatches` states three character equations
  for every h, for Q, upRight.dual and electronRight.dual. Each is the index
  of Hom_SM(R,K) minus the dual of Hom_SM(R.dual,K). These are not equations
  only about particle counts.
- `SharedPositive a` is the replacement sufficient condition. It is a
  condition on the signed index, not an assumed common quotient or operator.

The chosen positive coefficient gives a positive Hom-dimension difference
for each species separately. Irreducibility and compact semisimplicity
then give three splits onto the same S_i, without equating whole characters.
SM field extraction and the existing spinor/exterior construction derive the
actual subspaces in K and K.dual, their identifications, and nonzero descent.

There are **no T-unitarity, four-weight matching or actual conjugation premises
on this direct species-index endpoint**. It does not extract species indices
from dimensions or torus data. The compatibility encoded by D is still input.
Absent a way to verify the species equations and shared positive support for
a model, the endpoint does not apply automatically.

## Relationship To The Old Route

[SharedPositiveSpeciesIndex](../../../Physics/StandardModel/Spectrum/SharedPositiveSpeciesIndex.lean)
provides `of_common_index`: in the same normalized family, equality of the
Q/up/e characters and positive Q total dimension imply `SharedPositive`.
Character injectivity identifies coefficients, and positivity supplies a
shared positive one. Thus the old normalized common-index sufficient
conditions imply the new ones.

`of_conjugations` derives the same local positivity from the old two
conjugations, T-unitarity, four-weight matching and positive Q dimension.
Together with the unchanged species equations it feeds the new exterior
endpoint. No prior theorem is deleted or weakened. The new entry does not
claim that those old conjugation hypotheses allow arbitrary unequal species
indices; under their retained matching hypotheses the indices still agree.

## Controls And Scope

The [persistent audit](../../../Physics/StandardModel/Operators/Audit/AuditSharedPositiveQque.lean)
uses the normalized Circle family (trivial line, standard character z) and
three profiles

```text
I_Q = 1 - 2z,    I_up = 2 - 2z,    I_electron = 3 - 5z.
```

All share a positive trivial constituent. Their total dimensions are -1,
0 and -2, and Q differs from both other characters. A general control
realizes n-mz as a difference of actual continuous representations and
extracts a trivial-line split for every n > 0, irrespective of m. These
are representation-level controls, not a constructed ambient GUT source.

A separate profile with Q=1, up=z, electron=1 has positive total dimension
in every sector but no shared positive constituent. This proves that
individual positive counts alone do not supply the new condition; it is not
an independently formalized physical counterexample to all qque constructions.

The new condition is strictly weaker at the normalized-index data level.
No new phenomenologically viable model or broader concrete embedding class
is exhibited. No Wilson coefficient generation, anomaly consistency, decay
amplitude, lifetime or change to the E6 literature boundary is claimed.
The two-different-constituent proposal and MFV spurions are separate tasks.

See the [topic record](README.md) for verification and integration.
