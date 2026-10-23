# Explicit SM x H QQue Tensor

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Endpoint

The fourth tensor-extension milestone constructs a **nonzero invariant
functional on ordered internal fields**, with both SM gauge and residual H
invariance. Here SM denotes the covering product SU(3) x SU(2) x U(1), with
the existing integral `6Y` convention. This is not a Lorentz/Grassmann operator
or a nonzero interaction/amplitude theorem.

Write L_i for the actual mass-radical weight sector at monitored weight i.
The [compact light theorem](COMPACT_LIGHT_QQUE.md) derives

```text
f : Hom_H((L_0 tensor L_3) tensor (L_8* tensor L_14*), C), f != 0.
```

The new adapter adds explicit SM x H field identifications. Under these
additional inputs it derives

```text
Hom_(SM x H)((Q_light tensor Q_light) tensor
            (u_R_light tensor e_R_light), C) != 0.
```

Q_light is one and the same subrepresentation in both slots. Q_light lies
in the original mass radical; the two right-handed fields lie in its algebraic
dual. The output is on these supplied actual subspaces, not only on auxiliary
unitarized carriers.

## 2. Inputs and conclusion

### Additional Inputs

`CompactExplicitSMTensor.Decomposition` contains:

1. A full SM x H representation on the **unchanged radical** of the original
   T x H-invariant symmetric mass.
2. Agreement of this action with the original T x H representation after
   pullback along the existing physical covering-torus maps
   `PhysicalTorus.gaugeHom` and `PhysicalTorus.toTorus`. In particular,
   `residual_agrees` proves equality with the original residual H action.
3. A Q subrepresentation of that radical and right-handed up/electron
   subrepresentations of its dual.
4. SM x H representation equivalences
   `Q_light ~= Q_SM tensor L_0`, `Q_light ~= Q_SM tensor L_3`,
   `u_R_light ~= u_R_SM tensor L_8*`, and
   `e_R_light ~= e_R_SM tensor L_14*`.

These are genuine additional assumptions. The two Q equivalences identify
the same Q field with the two monitored multiplicity spaces. They are not
derived from four character equations, and the adapter need not apply when
other light SM representations overlap those weight spaces. No full-SM action
on the UV source, full-SM invariance of its mass, or automatic decomposition of
an arbitrary radical is proved here.

No nonzero coefficient, common irreducible constituent, or split projection
is included in this new structure. In `exists_qque`, the residual coefficient
is derived from the unchanged compact source hypotheses: two actual
conjugations, the four local index conditions, nonzero continuous Q target,
continuous compact H action, T-unitarity, and invariant symmetric mass.

## 4. Proof structure

### Construction

- [ExternalInvariantTensor](../../../../../Math/RepresentationTheory/Tensors/ExternalInvariantTensor.lean)
  combines invariant functionals for independent groups and proves that their
  tensor product is nonzero. Equivariant regrouping separates gauge and
  multiplicity factors without changing field order.
- [ExplicitSMResidualTensor](../../../../../Physics/StandardModel/Gauge/Tensors/ExplicitSMResidualTensor.lean)
  multiplies the checked nonzero SM color/weak epsilon contraction by the
  H-invariant multiplicity functional. `qque_tmul` gives this exact product
  on decomposable fields. `qque_ne_zero_iff` verifies that the construction
  cannot create a nonzero coefficient from zero input.
- `exists_on_fields` transports the result through the four explicit
  representation equivalences, retaining the same Q field in both slots.
  This algebraic construction accepts arbitrary H; compactness is needed
  only to derive the residual coefficient from the source in the next step.
- [CompactExplicitSMTensor](../../../../../Physics/StandardModel/Gauge/Tensors/CompactExplicitSMTensor.lean)
  composes the actual compact light-source theorem with that transport.

## 6. Scope and limitations

### Controls And Boundary

The [persistent physics audit](../../../../../Physics/StandardModel/Gauge/Tensors/Audit/AuditExplicitSMResidualTensor.lean)
checks nonzero SM x S3 and SM x A4 tensors with the existing two- and
three-dimensional sum-zero permutation representations as multiplicities.
More generally, matched multiplicities r,r,r*,r* work for any nonzero complex
H representation. These controls inhabit the explicit decomposed-field
construction; they do **not** construct a UV model or an inhabitant of the
additional radical-decomposition adapter.

The [mathematics audit](../../../../../Math/RepresentationTheory/Tensors/Audit/AuditExternalInvariantTensor.lean)
and physics audit reject all transitive axioms except `propext`,
`Classical.choice`, and `Quot.sound`, and enforce source-layer boundaries.

The [spinor/exterior extension](LORENTZ_EXTERIOR_QQUE.md) now proves nonvanishing
after explicit SL(2,C) spinor contraction and fermionic alternation, under
these same source and decomposition inputs. This is a separate stronger
endpoint; the ordered theorem above is unchanged.
Remaining tasks include constructing the added full-SM data for further
concrete sources and any dynamical or quantum-anomaly statement.
No duql extension or change to the E6 literature boundary is made.

Verification: [topic record](../../../../topics/explicit-sm-residual-tensor/README.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.

## Residual-action input filter

[ResidualQquePrefilter](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/ResidualQquePrefilter.lean)
uses the existing neutral physical exterior theorem on actual invariant
light Q/uc/ec subspaces with character-twisted SM equivalences. The dual
uc/ec ranges are the right-handed carriers. Prohibition covering every
admitted triplet requires a nontrivial qque residual character on each.
Equal-species characters and pointwise block neutrality give exclusions;
finite supplied triplet tests preserve protected parameter inputs when the
SM predicate and a decision procedure are supplied. Passing is not full B1
prohibition, and missing dictionaries give no protection evidence. This is
an input-filter consumer of existing nonzero evidence, not new independent
no-go coverage. The [topic result](../../../../topics/theorem-driven-protection-constraints/residual-prefilter-results.md)
records the explicit original-mass radical connection and SM-copy filter.

## Mixed cyclic Q pairs

[MixedQqueCyclicNecessity](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/MixedQqueCyclicNecessity.lean)
extracts the existing actual flavored exterior dictionary for arbitrary finite
cyclic flavor sets. Prohibition requires every mixed pair sum to be nonzero,
not only repeated-index sums. The Z3 three-generation control passes all
coordinate diagonal tests but has a nonzero mixed coefficient, including in
the actual signed four-family sector. This supplies additional filtering
coverage over diagonal coordinate tests, not a new completeness theorem or
UV realization. See the [result and limits](../../../../topics/sm-support-and-lfv-decomposition/su6-necessary-condition-results.md).

## Non-Abelian sample controls

[NonabelianQqueSamples](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/NonabelianQqueSamples.lean)
uses the existing matched split pairing on common S3/A4 three-dimensional
flavor factors, with actual left-to-right dual transport and nonzero exterior
descent. A4's lack of invariant flavor functionals does not eliminate the
four-field coefficient. The [sample record](../../../../topics/sm-support-and-lfv-decomposition/outside-class-sample-results.md)
separates the actual SU(6) tensor branching connection from the unconstructed
mass/VEV/radical realization. This is a concrete application of existing
common-factor results, not a new independent no-go or arbitrary non-Abelian
support classification.

## Unequal SM-preserving S3 actions

[S3QqueTensorSamples](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/S3QqueTensorSamples.lean)
proves opposite actual qque outcomes for (permutation,trivial,sign) and
(permutation,sign,sign) three-dimensional flavor representations. Basis
transpositions plus Q symmetry prove the zero result; two sign factors cancel
in the nonzero witness. Q/sign common constituents are absent. The
[result](../../../../topics/sm-support-and-lfv-decomposition/sm-preserving-sample-results.md)
records independent SM commutation, failure of the common uniform flavor
dictionary and the conditional neutral-Higgs flavor-map gate. This remains a
selected physical sector, not a full protecting SU(6) construction.

## S3 sample passing bijective flavor-map gates

[S3YukawaCompatibleQque](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/S3YukawaCompatibleQque.lean)
fixes Q,uR,dR to permutation flavor and L,eR to three sign copies, with a
residual-neutral Higgs. Species flavor actions commute with the independent
SM gauge action; the quark action is noncommuting. Bijective invariant maps
Q→uR, Q→dR and L→eR pass the specified flavor-map gates. The explicit symmetric
coefficient det(ones,x*y,z) sum(r) is invariant and evaluates to 1 at a basis
tuple, so the existing physical exterior equivalence proves actual qque
allowance. The [result and boundaries](../../../../topics/s3-yukawa-compatible-qque/results.md)
separate this selected-sector certificate from physical Yukawa matching,
realistic spectra/mixing, all-sector classification and UV realization.
