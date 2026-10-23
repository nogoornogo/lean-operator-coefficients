# Normalized Li D.6 Duue Basis Certificate

## Result

The conjugate normalized local interpretation of Li D.6, including symmetric
and alternating repeated-U flavor components, exhausts the independently
defined right-DUUE exterior sector. Actual raw exterior descent equals the
complete inverse; this is stronger than matching a count.

Sources: [conventions](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/LiDuueConvention.lean),
[certificate](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/LiDuueCertificate.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/Audit/AuditLiDuueBasis.lean).

## Inputs, Conjugation And Citation Role

U,D,E are arbitrary complex flavor modules with specified representations of
an arbitrary abstract residual group H. No compactness, continuity or finite
dimension is required for the complete residual Hom theorem.

[Li et al., v2 PDF page 50, D.6](https://arxiv.org/pdf/2201.04639v2#page=50)
prints D,E,U,U with left spin and two U symmetry types. It supplies candidate
data, not a completeness premise. The positive repository sector uses the
conjugate local expression in normalized right-spinor coordinates. Conjugation
of scalar local factors is proved. Identification of physical antiparticle
flavor spaces is not inferred: a model supplies equivariant identifications
or the existing signed-sector semilinear conjugation data. See the
[dictionary](../../../../topics/li-duql-duue-basis/source-recovery.md).

## Proof Structure And Normalization

Reorder D,E,U,U to U,U,D,E is even; color cycling is even. The symmetric
printed seed becomes the cross pairing, the alternating seed the direct
pairing. For unrestricted residual k the sources are
`S=-(k+swap k)/2`, `A=(k-swap k)/4`. `source_symmetries` proves their types.
`ordered_apply` proves the literal sum of both printed contractions.

`candidate` is raw exterior alternatization of those ordered seeds. Color and
Fermi signs cancel under U exchange. `local_reconstruction` and
`restriction_candidate` recover `(k,-k-swap k)`; `candidate_eq` identifies this
actual descent with the independent completeness inverse. Both extraction and
reconstruction identities are proved. No factorial normalization is assumed.

## Finite Coordinates And Applicability

Nonredundant coordinates are indexed by `(I_U × I_U) × (I_D × I_E)`.
They are not restricted to symmetric U entries. `finiteEquiv` retains all H
equations on interpolated functionals; `finite_inverse_is_candidate` proves
actual candidate agreement. Both inverses are included in the equivalence.

When the flavor tensor action is trivial, the coordinate basis is independent
and spanning, and each element is a mapped literal candidate. `flavor_finrank`
gives `n_U*n_U*n_D*n_E`: equal flavor counts three give 81, one gives 1, and
an empty species gives 0. The audit checks finite index controls in the kernel.
These counts do not assert an invariant dimension for nontrivial H.

## Four-Family Connection, Scope And Verification

The shared composition transports the actual DUUE candidate through its
residual equivalence into the derived signed-species family. Equality with
the existing reconstruction and both total inverse identities are proved.
No complex-linear identification of opposite lepton degrees is claimed.

ABC4EFT runtime arrays, general amplitude correspondence, p/y/m/j algorithms,
derivatives, EOM/IBP, matching and rates are excluded. Strict transitive audits
permit only `propext`, `Classical.choice`, `Quot.sound`. Commands and outcomes
are recorded in the [shared topic](../../../../topics/li-duql-duue-basis/README.md).
