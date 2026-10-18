# Model-Independent Actual-Mass / Physical Qque Bridge

## Shared Statement

[PhysicalCommonCopyModel](../../../Physics/FieldTheory/Mass/PhysicalCommonCopyModel.lean)
contains the shared physical theorem, with no SU(5) matter carrier, branching,
copy count or unified-group parameter. H is any group; S and T are finite-dimensional
complex common-copy representations, only S is semisimple, and dim S > dim T.
The actual field space F and its SM-cover × H representation rho are arbitrary
complex representations. No topology, continuity, compactness, invariant metric
or target semisimplicity is required.

A `Species` realization supplies an injective equivariant full-copy embedding i,
a copy intertwiner M : S → T, and an actual dual-field map j satisfying

```
B.toIntertwiningMap ∘ i = j ∘ (id_gauge tensor M).
```

There are three such squares, for Q, up-left and electron-left, with common S/T
and independent Mq/Mu/Me. This is a structural relation to the original symmetric
mass B. It does not supply light membership, a common kernel constituent, a
projection on all light fields, or a nonzero coefficient.

`Realization.light_exterior` derives injective kernel embeddings, their actual
ranges in B's radical, the restricted ambient SM/H action, and a nonzero physical
qque exterior coefficient on Q's range and the right-handed duals of the actual
up-left/electron-left ranges. The physical coefficient includes Lorentz invariance
and fermionic alternation through the existing shared exterior construction.
H acts trivially on the Weyl spinor factors in this construction.
`Species.range_action` checks that the range action is the actual ambient action,
not an unrelated representation transported to a vector space of equal dimension.

`Model` packages a derivation of these squares for **every** invariant symmetric
mass on a fixed matter/action model. `Model.arbitrary_mass_light_exterior` is
therefore the reusable arbitrary-mass theorem. To use it for a new model one must
prove its realization interface; arbitrary matter content need not realize it.
This obligation is not inferred from dim S > dim T or a group embedding alone.

## Derived Normal Forms And The SU(5) Consumer

`speciesOfDirac` is a generic constructor: a proved exact Dirac normal form for
original B and source/target species diagrams imply its mass squares. Its actual
Dirac target is finite-dimensional for the bidual identification; the shared
realization endpoint imposes no finite-dimensionality on F. Its input
is an exact structural equality, not an assumed zero-mode placement. This is a
sufficient constructor; the shared realization theorem itself does not require
B to be Dirac on the entire field space, and additional decoupled sectors are
permitted if the same squares can be proved.

[PhysicalCommonCopyAdapter](../../../GUT/SU5/SelectionRules/PhysicalCommonCopyAdapter.lean)
derives `model` for the existing `(Ten tensor S) + bar-five + (Ten tensor T)*`
carrier. It uses the checked SU(5) branching, arbitrary invariant-mass normal
form and derived residual-equivariant species maps. Thus its public arbitrary-B
endpoint has no supplied Dirac ansatz, mass square or light certificate. Its
final implication directly calls the shared `Model` theorem. Earlier named
SU(5) endpoints remain valid compatibility results.

The common kernel/isotypic argument and the entire actual-range physical
implication now live in Math/Physics. SU(5) remains solely a checked model
realization. A model with another unified group can reuse the shared theorem
once its actual SM branching, common-copy embeddings and mass squares are proved.
No verification of SU(N), Spin(10) or E6 matter realizations is claimed here;
the existing E6 literature boundary is unchanged.

## Dependency And Interpretation Boundaries

The shared audit rejects every current GUT-layer import and every original
SU(5)/SU(6) module origin. A previously unused import from `SMEpsilonTensor`
through `StandardModelLocalOperator` to the SU(5) Weyl-orbit module was removed;
the determinant, complex and Circle library dependencies are now direct.
The existing embedding audit also drops a now-unused `open Math`; all of its
checks and the original-origin exclusion are unchanged. Declaration names in
the shared historical GUT namespace do not indicate a model-layer import.

The theorem concerns the participating light ranges, not extension of the
coefficient to the whole radical. Common S/T, source semisimplicity, positive
dimension difference, the unbroken SM-cover action and the model realization
remain explicit. Global quotient descent and a UV derivation of the residual
copy action remain model obligations. Nonzero allowed coefficient space means
symmetry does not forbid this coefficient; it does not prove generation by UV
matching, a decay amplitude, a lifetime or all-BNV protection.

See [plan](model-independent-plan.md), [remaining connections](remaining-general-connections.md)
and [verification](verification.md).
