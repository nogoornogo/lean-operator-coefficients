# Audit Of The Remaining Concrete Inputs

## Frozen Audit Endpoint

Inspect the supplied covariant model and its consumers for a concrete candidate,
a mass/VEV relation, actual-light SM identification, physical support and a
residual-Hom vanishing proof. Record what can be verified from the present
source, without adding assumptions or starting automorphism/extension
classification. This phase is source/documentation inspection, not a new Lean
proof or a new proof-build baseline.

## Findings

| Condition | Present evidence | Missing evidence / acceptance gate |
| --- | --- | --- |
| Genuine noncommuting candidate | `Model` specifies alpha, beta and genuine residual representations; consumers quantify over M | A concrete construction with checked group law, unitary/continuity data and an identified noncommuting action |
| Unbroken gauge group and vacuum | Injective continuous K embedding, normalization and a fixed VEV are fields of `Model` | For an application claiming the exact SM unbroken group, prove the intended stabilizer and cover dictionary; fixed VEV alone permits a larger stabilizer and zero VEV |
| Mass from the chosen scalar/VEV | K/H-invariant symmetric mass is supplied independently | If mass realization is part of the chosen physical model, construct its invariant scalar coupling/family and prove evaluation at the VEV gives this mass; this is not a consequence of the present structure |
| Actual-light SM fields | Radical preservation is derived; positive/resolved target predicates are exposed | Prove a full-field or supported-sector intertwining equivalence on the actual radical, specifying extra vectorlike/singlet content; gauge index alone is insufficient |
| Lorentz presentation | Covariance is proved on the gauge-only fourth exterior power | Construct the spinor-enriched field carrier, its Lorentz/local action and residual covariance, respecting chirality and conjugation conventions |
| Physical BNV support | `Support` requires an independently supplied unsupported submodule stable under K and H | Define unsupported inputs from the physical signed-species/BNV dictionary and prove preservation by the specific candidate |
| Protection | Two-sided descent and Hom-zero iff are proved | Compute or prove zero of the residual Hom for that actual physical carrier/support; no such instantiated calculation is present in the inspected candidate framework |

The [model source](../../../GUT/SU6/SelectionRules/Models/AutomorphismCovariantModel.lean)
contains no equation linking `mass` with `vev` or a Yukawa/scalar family.
Its `vev_gauge` and `vev_residual` prove fixedness, not equality of the chosen
K with the full stabilizer. These are explicit interface boundaries, not errors
in the already proved conditional descent theorems.

The [support source](../../../Math/RepresentationTheory/AutomorphismCovariantExterior.lean)
contains only a submodule and local/residual stability certificates. There is
no baryon-number predicate, Lorentz field or SM species dictionary in that
structure. The [SU(6) specialization](../../../GUT/SU6/SelectionRules/Models/CovariantFourFermion.lean)
retains these application inputs. For example, the whole exterior carrier is
stable under both actions and could be designated unsupported. Requiring a
functional to vanish on that whole carrier forces zero by definition; that
would not demonstrate physical BNV prohibition. This is a source-level
boundary observation, not a newly audited Lean counterexample declaration.
The physical support must be fixed independently before its Hom-zero test.

The [gauge-index ambiguity proof](compatibility-result.md) already shows why
the missing full-field equivalence cannot be inferred from the positive gauge
index. It supplies no enlarged UV model and does not disprove the existence
of a valid equivalence for a particular mass radical.

## Inspection Evidence And Reproduction

Inspect the declarations and all references found by:

```sh
rg -n 'AutomorphismCovariantModel|CovariantFourFermion|HasPositiveDualTarget|HasResolvedDualTarget' Math Physics GUT
rg -n 'Model H K|: Model|Model.mk|HasPositiveDualTarget|HasResolvedDualTarget|CovariantFourFermion.Support|ofGenerators' GUT/SU6/SelectionRules/Models Math/RepresentationTheory/AutomorphismCovariantExterior.lean
```

The covariant framework references resolve to its definition, audits and
parameterized tests in `ChargeReversingCandidate`, `TargetIndexCompatibility`,
`InnerDefectCandidate`, `GaugeEquivalentCandidate` and `CovariantFourFermion`.
The inspected consumers take M (and support where required) as parameters;
none constructs the complete candidate and certificates in the table. Other
historical/commuting model constructors are not automatically constructors of
this covariant interface. This is scoped source-inspection evidence, not a
formal nonexistence theorem or a claim that Lean cannot construct a model.

## Outcome And Next Concrete Deliverable

The remaining conditions are now identified with explicit acceptance gates.
They are **uninstantiated**, not proved false. Existing generic implications
and strict audits do not prove these premises.

The next useful deliverable is one candidate specification containing H, alpha,
UV fermion/scalar representations, K and its embedding, VEV, mass (with any
required realization), and the intended actual-light SM sector. After its
normalization and radical dictionary pass, define its spinor/BNV support and
compute residual Hom. Any new physical restriction, such as removing all extra
vectorlike light fields, must be stated and verified rather than inferred.
Adding another conditional criterion alone does not close these inputs.

This inspection is complete within its frozen endpoint. The wider protection
search remains in progress and has no protecting solution. General
classification and physical rates remain outside scope; no master merge.

## Verification

Documentation-only changes: local Markdown links and `git diff --check` passed.
No Lean build or new axiom audit was rerun in this phase. The previous 6,575-job
build belongs to the unchanged Lean source state recorded in
[the compatibility result](compatibility-result.md).
