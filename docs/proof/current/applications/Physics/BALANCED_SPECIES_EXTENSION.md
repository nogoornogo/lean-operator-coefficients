# Balanced Species Extensions

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Derived Result

Character additivity cancels Z_R and proves equality of the three actual
species indices with the reference. The reference spectrum and conjugations
identify the Q/up/e characters and give positive Q dimension. The new
radical's automatic normalized presentation therefore has a common positive
constituent, hence pairwise positive support. The existing automatic-species
endpoint supplies participating fields in K/K.dual and a nonzero qque
alternating/exterior coefficient under SM-cover x H x SL(2,C).

Only the new action's continuity is an explicit premise of this API; a
separate continuity premise on the reference is not needed in the proof.
Zero mass is not required on either source. Nothing identifies the two
masses or proves that a particular UV mass realizes the input spectrum.

The identity extension is constructed, recovering the old exact-spectrum
sufficient package. Index cancellation also composes through two extensions.
`not_exact_of_quark_extra` proves that an extension with positive-dimensional
Z_Q cannot satisfy the old exact-SM-plus-singlets spectrum for ANY generation
or singlet counts. This is conditional on the extension certificate: it is
not a constructed nonzero-extra ambient benchmark.

## 2. Inputs and conclusion

### Statement

An alternative sufficient-condition package allows extra light matter while
deriving, rather than assuming, positive support of the automatic species
indices. It compares a new actual mass radical K to an exact-SM reference K0.
The ambient groups and mass forms of the two sources may differ; H is shared.

The reference has n > 0 exact left-chiral SM generations plus singlets,
T-unitarity and two actual conjugations. The new source retains the usual
finite-dimensional ambient/mass carrier and a compatible jointly continuous
SM-cover x H action on K, with compact H. No exact spectrum, T-unitarity,
four-weight target or conjugation is required of the new source.

For each R in {quark, upRight.dual, electronRight.dual}, write

```text
M_R(K) = Hom_SM(R, K).
```

Supply an additional finite-dimensional H representation Z_R and actual
H-equivariant linear equivalences

```text
M_R(K)             ~= M_R(K0)             + Z_R
M_(R.dual)(K).dual ~= M_(R.dual)(K0).dual + Z_R.
```

Here `+` denotes a direct sum; the SAME Z_R occurs on both lines, including
its H action. The three Z_R may differ and may be zero. The Lean certificate
uses coordinates `Fin d -> C` for Z_R, with an unrestricted representation.
These are spectral decompositions, not supplied character equations,
irreducible splittings, positive-index assumptions or nonzero coefficients.
They do require proof when applying the theorem to a model.

## 6. Scope and limitations

### Boundaries

- Merely SM-vectorlike counts do not ensure the two H representations agree.
- This retained theorem takes multiplicity equivalences as inputs. The
  [global vectorlike entrance](../../inputs/Physics/VECTORLIKE_SPECTRUM.md) now constructs them
  from K = K0 + X + X.dual with continuous X and supplies a concrete extra-field
  source. That stronger adapter is not inferred from SM-only particle counts.
- Only the three indicated species are constrained. Additional fields must
  respect their multiplicity decompositions; this is not permission for
  arbitrary changes to the monitored species indices.
- This enlarges the sufficient spectral entrance, not the general
  pairwise-positive theorem's conclusion. It is not a non-SU(5) embedding
  classification or a theorem of unavoidable proton decay.
- The normalized presentation remains noncomputable. No new anomaly,
  Yukawa, vacuum, Wilson-coefficient or lifetime result is claimed.

## 7. Sources and verification

### Sources

- [Algebraic cancellation](../../../../../Math/RepresentationTheory/Multiplicity/BalancedMultiplicityExtension.lean)
- [Actual species and positive support](../../../../../Physics/StandardModel/Spectrum/Representations/BalancedSpeciesExtension.lean)
- [Actual exterior endpoint](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/BalancedSpeciesQque.lean)
- [Plan and verification](../../../../topics/balanced-species-extension/README.md)

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
