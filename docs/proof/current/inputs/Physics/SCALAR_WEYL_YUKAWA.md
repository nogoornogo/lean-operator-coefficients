# Scalar/Weyl Yukawa Input

`Physics.YukawaModel.model kappa massSquared mass yukawa` supplies the existing
four-direction mixed source with actual SL(2,C) action. Its total density has
scalar and paired Weyl kinetic terms, scalar/fermion masses and both chiral
Yukawa terms. Conjugate labels are independent complex generators. One even
label is the scalar; the other three remain unused spectators with zero EOM.

Generated odd equations equal kappa times the opposite-chirality kinetic
equation, minus same-chirality mass and scalar-times-Yukawa epsilon terms.
The scalar equation is minus the wave field, scalar mass term and both pair
Yukawa terms. All parameters are complex without a nonzero premise. Setting
masses and Yukawa couplings to zero recovers the free Euler family.

The proof computes these equations from the total syntax, proves their
covariance and applies the general Euler-span stability theorem.
`full_relations` identifies the relation space with the differential closure
of an independently written family plus linear IBP. Complete all-order
coordinates and exact selections come from the model package.

The DHM consumer also compiles the paper component syntax directly, proves
its Euler-family and full-relation equality with the registered model, and
transports coefficients with unchanged evaluations.

Density symmetry is proved independently: the paired kinetic uses invariant
coevaluation, the scalar kinetic uses the existing Lorentz metric theorem,
and the same-chirality pair uses the determinant-one epsilon identity.

- [Density and Euler calculation](../../../../../Math/Algebra/Constructions/ScalarWeylYukawa.lean).
- [Model and full relations](../../../../../Physics/FieldTheory/Jets/Lagrangian/YukawaModel.lean).
- [Density symmetry](../../../../../Physics/FieldTheory/Jets/Lagrangian/YukawaDensitySymmetry.lean).
- [Literature/artificial comparisons](../../../../topics/lagrangian-model-connections/literature-validation.md).
- [Input guide](../../../../topics/lagrangian-model-connections/input-guide.md).

No local gauge connection or reality quotient is imposed. This is an algebraic
coefficient input, not a quantized theory, scattering calculation, universal
finite solver or preservation of earlier free-sector counts under arbitrary
interactions. The [automatic connection](../../../../../Physics/FieldTheory/Jets/Lagrangian/EulerDensityConnection.lean)
now derives the same input from density invariance using the general
[Euler naturality theorem](../../core/Math/EULER_NATURALITY.md).
