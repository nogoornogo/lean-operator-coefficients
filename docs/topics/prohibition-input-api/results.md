# Input-Side Prohibition API Results

## Generic Input and Composition

`Math.ProhibitionInput.Forbids` names `SelectionCriteria.Forbidden` on the
existing actual selected coefficient space. `AllForbids` quantifies both
fermion and scalar degrees without a cutoff. The API uses the existing typed
local/residual actions and stable `Spec`; no new model bundle or completeness
premise is introduced. `factors_iff` reuses `ComposableProtection.forbidden_iff`.

`factor`, `mono`, `all_mono`, `union_iff`, `all_union_iff`, `iUnion_iff` and
`all_iUnion_iff` support projections and changing targets on one admitted input.
Indexed unions permit arbitrary index types, including empty types.
`empty_forbids` and `transport` handle empty requests and certified equivalences.
Finite species alphabets are inherited; coefficient carriers need not be finite
dimensional.

## Necessary Conditions

`no_shared` extracts absence of a common irreducible constituent from a
selected factor. `no_shared_iff` requires source semisimplicity for each selected
factor; `shared_defeats` supplies the contradiction consumer. The representation
is the actual `TypedMixedSeparatedHom.residual`, after local and statistics
relations. No raw-tensor constituent is assumed to survive that quotient.

`ScalarProhibitionNecessity.forbidden_iff_detect` proves, for an explicitly
scalar action on a nontrivial complex vector space, that invariant-functional
vanishing is equivalent to a detecting group element. The neutral converse
constructs a nonzero dual functional using mathlib's
`Module.Projective.exists_dual_ne_zero`; vector spaces supply projectivity.
No finite-dimensionality is needed. `charge_detected` applies this to the
actual admitted residual carrier using the existing quotient scalar-action
bridge. Nontriviality of that carrier remains an explicit instance premise.
`zero_carrier_forbidden` and `neutral_zero_control` show why dropping it is
invalid: neutrality on a zero domain still permits prohibition.

`restriction_obstruction` applies to the existing selected restriction map:
forbidden larger-group source and an allowed smaller-group target imply that
map is not onto. This is separate from `Protected`, which describes preservation
of every smaller-group coefficient. The generic `not_surjective` lemma is
available for other certified coefficient maps.

## Bounded Physics Consumer

`GUT.ProhibitionInputSM` reuses `ComposableBLSupport.Input` and provides
`Forbids`, `AllForbids`, `facade_iff` and `residual_iff`. Koren/BGW certificates
are regressions for sufficient simultaneous prohibition; no model classification
is inferred. DGT retains both all-degree baryon prohibition and its distinct
dipole restriction obstruction. Quarticity retains SM/Higgs L2 prohibition
alongside an allowed dressed nuR/eta coefficient on a different alphabet.

`llhh_forbidden_iff` uses the actual `WeinbergSMInterface.ModelSector` and
its existing coefficient equivalence: for one complex lepton flavor copy and
neutral Higgs flavor, prohibition is equivalent to some `(a g 1)^2 != 1`.
This is a square-action criterion, not a claim that every nontrivial lepton
charge forbids LLHH. Charged Higgs cases retain their existing separate bridges.

## Endpoint and Limits

The frozen implementation is complete with the passing checks in
[verification](verification.md). No new local nonzero-admission foundation was
needed. Model-dependent actions, admission, nontriviality and semisimplicity
remain supplied inputs. There is no automatic UV model search, classification
of mass/light spectra, derivative/EOM/IBP extension, anomaly calculation,
matching, generated interaction or rate claim. No dependency pins changed.
