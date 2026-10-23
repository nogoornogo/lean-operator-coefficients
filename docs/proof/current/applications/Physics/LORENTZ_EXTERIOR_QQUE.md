# QQue Spinors And Exterior Coefficient

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Statement

The compact residual-source assumptions and explicit compatible SM decomposition
from [the ordered adapter](EXPLICIT_SM_RESIDUAL_TENSOR.md) imply a nonzero
invariant functional on the fourth exterior power of

```text
V = (Q_light tensor S_L) direct-sum
    (u_right_light tensor S_R) direct-sum (e_right_light tensor S_R).
```

The acting group is `(SM_cover x H) x SL(2,C)`. The left spinor action is
the defining two-dimensional action; the right action is its entrywise complex
conjugate. Both preserve their epsilon pairing. No identification theorem
between this explicit SL(2,C) group and a separately defined Lorentz cover is
used or asserted.

The stronger endpoint `CompactLightExteriorQque.exists_ordered_nonzero_exterior`
exhibits an invariant coefficient on the ordered `Q,Q,u_right,e_right` spinor-field
tensor whose alternating descent is nonzero. Thus the theorem does not merely
find an unspecified invariant in the exterior power. `exists_qque` packages
the resulting nonzero intertwiner `exteriorPower 4 V -> C`.

There is now a separate source-derived route:
`LightSMSpeciesQque.exists_actual_alternation` / `exists_actual_exterior`.
Instead of supplying the field decomposition, it assumes a compatible
continuous SM-cover x H action on the same radical and three SM-species
index equations in addition to the four-weight source conditions. Evaluation
images and dualized equivariant splittings construct the actual fields and
their identifications. See [its implementation and audits](../../../../topics/full-sm-light-bridge/implementation.md)
and [the distinct input package](../../../ASSUMPTIONS.md).

### Pointwise-Neutral Unit-Flavor Route

[NeutralQqueExterior](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/NeutralQqueExterior.lean)
provides a separate algebraic route for genuine Circle-valued species characters
of an Abelian H. The pointwise formulas `Q=a c w`, `u^c=a c²`, `e^c=a w²`
imply neutral qque without group laws for the auxiliary functions a,c,w.
`coefficient_witness` evaluates the explicit unit-flavor fermionic exterior
coefficient to **2**. `exists_on_fields` transports this named coefficient
through supplied species equivalences and preserves nonvanishing. No compact
common-residual-constituent premise is used in this route.

The [SU(6) scalar/block consumer](../../../../model-studies/su6-protection/scalar-block-obstruction.md)
constructs the relevant species equivalences on actual benchmark zero-mode
subspaces and proves their SM/residual action compatibility. Its fixed placement,
exact mass and pointwise scalar/block hypotheses are separate admission
conditions; they do not follow from an arbitrary positive gauge index.

## 2. Inputs and conclusion

### Unchanged Inputs

- Finite-dimensional complex matter, commuting ambient G and residual H actions,
  T-unitarity, T x H invariant symmetric mass, and two actual conjugations.
- Compact topological H, continuous source H action and nonzero continuous
  finite-dimensional Q target, with four local index equations at 0, 3, 8, 14.
- `CompactExplicitSMTensor.Decomposition`: actual SM x H subrepresentations
  of the original radical (Q) and its dual (right-handed up/electron), with
  compatible covering-torus restriction and full field identifications.

The full-SM adapter is still additional input, not a consequence of torus
matching. Its Q identifications at 0 and 3 concern the same actual Q space.
The new construction uses its identification at 0 twice; it does not require
that two separately chosen Q projections coincide. The retained adapter's
identification at 3 is accepted but not used in this last assembly step.

Neither a nonzero coefficient nor a common quotient, splitting, exchange
certificate, generation lower bound beyond nonzero Q, or coupling is assumed.
The compact-source theorem derives the common nonzero quotient and splits.

## 4. Proof structure

### Construction And Nonzero Witness

1. Extract a common nonzero residual quotient R of actual sectors 0, 8 and 14
   using the existing compact four-weight source theorem.
2. Use one Q splitting in both slots and symmetrize the residual coefficient:
   `u(x)e(y) + u(y)e(x)`, after the derived projections. It equals 2 at
   `x=y`, `phi(x)=1` on the embedded quotient vectors and duals.
3. Multiply by the color, weak, left-spinor and right-spinor epsilon contractions.
   Swapping Q slots introduces three minus signs, not two, including the left
   spinor pairing. The resulting contribution survives fermionic alternation.
4. Project a multilinear coefficient from the sum of the three species and
   alternate over all 24 permutations. This constructs an actual alternating
   map, hence a linear functional on the fourth exterior power.
5. Evaluate on the distinct components
   `Q_(color0,weak0,left0)`, `Q_(color1,weak1,left1)`,
   `u_(color2,right0)`, `e_right1` using the same quotient vector in both Q
   factors. The value is **4** with the unnormalized symmetric residual
   coefficient. Four different generations are not needed.
6. Transport along the given species-preserving SM x H equivalences and their
   spinor extensions. Exterior descent commutes with this transport; its
   invertibility preserves nonzero evaluation on the actual light fields.

## 6. Scope and limitations

### Boundary

This closes the local algebraic spinor/fermionic-alternation bridge for the
specified qque adapter. The output is an invariant **functional**, not an
interchangeably asserted vector in the original exterior power. The "whole
field space" here is the direct sum of the three participating species,
including all their gauge, residual and spinor components, not a four-component
projection or the entire ultraviolet matter representation.

It does not construct a quantum field operator, a nonzero generated interaction,
Wilson coefficient, decay amplitude or lifetime. No unconditional arbitrary-radical full-SM
decomposition, exact quantum anomaly cancellation, Lorentz-cover classification,
duql exterior theorem or new E6 global-form result follows. Prior torus-only
endpoints retain their boundaries.

Verification and integration: [topic record](../../../../topics/qque-lorentz-exterior/README.md).

## 7. Sources and verification

### Sources And Audits

- [Four-slot alternation and transport](../../../../../Math/RepresentationTheory/Exterior/FourSlotAlternation.lean).
- [Symmetric residual coefficient](../../../../../Math/RepresentationTheory/Symmetric/SymmetricInvariantPairing.lean).
- [Explicit spinors](../../../../../Physics/FieldTheory/Spinor/Weyl/WeylSpinor.lean).
- [Combined coefficient and evaluation](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/QqueSpinorExterior.lean).
- [Actual compact-source endpoint](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/CompactLightExteriorQque.lean).
- [Strict mathematical audit](../../../../../Math/RepresentationTheory/Exterior/Audit/AuditFourSlotAlternation.lean).
- [Endpoint and one-generation/S3/A4 audit](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/Audit/AuditCompactLightExteriorQque.lean).

These controls instantiate the matched-field construction. They do not construct
new UV models or new inhabitants of the full radical-decomposition adapter.

The exact [integer test](../../../../../tools/qque/audit_one_generation.py) compares all
4! slot permutations on all increasing four-element subsets of the 20
one-generation field components against the independent Grassmann expansion.
It gives 24 nonzero monomials with coefficients of absolute value 4 for the
new symmetrized construction. The earlier unit-flavor construction retains
absolute value 2: the difference is the explicit factor `1*1 + 1*1 = 2`.
This finite test is independent corroboration, not an input to the Lean proof.
See [test instructions](../../../../../tools/qque/README.md) for its command and limits.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes belong to their linked checkpoints. The
pointwise-neutral extension has its own [verification record](../../../../topics/su6-twisted-protection/generalization-result.md).
