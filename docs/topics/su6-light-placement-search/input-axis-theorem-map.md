# Existing Theorem Routes and Their Application Inputs

This map is a documentation inventory of existing proof routes, following
integration of the SU(6) exploration. It introduces no theorem or automatic
input classifier. Read it before generating candidate fields or operators.
A failed applicability check means **undetermined**, not protected.

## Input information to record

| Axis | Cases to distinguish | Required evidence |
| --- | --- | --- |
| Residual action | Ambient commuting product action; specified automorphism-covariant action; action not yet specified | Actual action and compatibility laws, not just numeric charges |
| Embedding | Standard SU(5) chain; other embedding with the required actual conjugations; other or unidentified embedding | Embedding and weight dictionary; conjugating elements where used |
| Light/mass information | Actual radical with field dictionary; only its dual-index target identified; no established radical/index connection | Invariant symmetric complex-bilinear mass and the relevant identification |

These are evidence categories, not disjoint model classifications. An exact
radical dictionary also yields weaker index evidence; an alternative embedding
may still have the required conjugations. "Not identified" is lack of proof,
not a physical property. No finite count or coverage percentage follows.

## Existing proof routes

The following rows are **overlapping theorem routes, not cases of a model-space
partition**. Completing their application inputs would not establish coverage
of all models. R1–R7 correspond to the first seven rows of the earlier table.
The former last row is now the separate undetermined-input section below.

### Ambient symmetry and mass-index routes

| ID | Applicability | Proved result | Model inputs still needed | References |
| --- | --- | --- | --- | --- |
| R1 | Ambient commuting action and standard SU(5) chain | Profile compatibility; exclusion of the specified nonzero-qque pure charge targets | Actual ambient action and embedding; the requested radical dual index is the target being tested | [StandardChain](../../../GUT/Common/StandardChain/StandardChain.lean), [SU6 connection](physical-index-results.md) |
| R2 | Ambient commuting action and the required torus conjugations | Local dual-index matching gives neutral supported signatures and actual weight support under the endpoint's positive-target assumptions | Actual conjugators, invariant mass, local target and compatible full-SM field dictionary for a physical coefficient conclusion | [Partial target](../conjugation-partial-target/README.md), [two conjugations](../two-conjugation-qque/README.md) |
| R3 | Ambient commuting action, required conjugations, and finite or compact-continuous residual H | Four-weight character target yields a nonzero residual tensor functional | Actual mass/target and compatible full-SM radical/dual field dictionaries; compact route also needs its continuity assumptions | [Compact light qque](../../proof/current/applications/Physics/COMPACT_LIGHT_QQUE.md), [four-weight routes](../four-weight-qque/README.md) |

For R2/R3, the generic extensions to physical coefficients already exist:
[SM/residual tensor](../explicit-sm-residual-tensor/README.md),
[Lorentz/exterior](../qque-lorentz-exterior/README.md), and
[exact SM spectrum](../exact-sm-spectrum-qque/README.md).
The full-SM dictionary is an application input; it is not derived from a
four-weight target alone. Thus these rows do not by themselves define new
generic adapter work. A concrete model is needed to identify a missing proof.

### Actual-field and mass-presentation routes

| ID | Applicability | Proved result | Model inputs still needed | References |
| --- | --- | --- | --- | --- |
| R4 | Admitted compatible SM/residual action on the full light Q/U/E fields | Exact qque zero/nonzero criterion under the chosen endpoint's hypotheses | Actual full light fields and their actions; source semisimplicity for the shared-constituent version | [Full light criterion](../qque-full-species-boundary/README.md), [common constituent](../qque-common-irreducible/README.md) |
| R5 | Admitted mass-independent sector presentation | Common irreducible Hom surplus in each species gives actual light ranges and a nonzero physical qque coefficient for every admitted mass | Sector decomposition, pairing exclusions, semisimplicity and constituent surplus | [Species copy surplus](../../proof/current/applications/Physics/SPECIES_COPY_SURPLUS_QQUE.md) |
| R6 | Specified scalar/block compensation on the fixed SU(5) or SU(6) standard placement | Physical qque nonvanishing in the admitted classes; a separate fixed-Yukawa theorem forces light inclusion | Actual action, carrier and participating light maps or the specified benchmark mass | [SU5 scalar/block](../../proof/current/applications/GUT/SU5_SCALAR_BLOCK_QQUE.md), [SU6 class](../su6-twisted-protection/generalization-result.md), [fixed Yukawa family](results.md) |

R4 can decide qque prohibition as well as nonvanishing. Shared constituents
refer to the product representations in its criterion, not necessarily to
individual Q/U/E. Qque vanishing alone does not establish total B1 prohibition.
R5/R6 give sufficient nonvanishing conditions; failure of their hypotheses
is not a prohibition certificate. Forced light inclusion alone does not
prove nonvanishing under a newly proposed residual action.

### Covariant-action route with unresolved general classification

| ID | Applicability | Proved result | Remaining gap | References |
| --- | --- | --- | --- | --- |
| R7 | Specified automorphism-covariant action, normalized gauge embedding and actual radical/support dictionary | Radical preservation and coefficient transport; exclusion of certain reversing or target-index-incompatible candidates | No general noncommuting-action exclusion or protecting-model existence classification | [Covariant interface](../su6-twisted-protection/interface.md), [compatibility test](../su6-twisted-protection/compatibility-result.md), [probe/defect test](../su6-twisted-protection/defect-result.md) |

Outer automorphisms, antilinear actions, lifts outside the specified unbroken
group, and non-split extensions must be distinguished before selecting a
new task. These descriptions can overlap; they are not yet a disjoint partition.
The complex-linear interfaces must not be assumed to cover antilinear actions.

## Undetermined inputs: not an additional model class

The former last row described missing evidence, not a class to exhaust by
brute force. An input is undetermined when no route's application hypotheses
have been established, or when the relevant theorem itself is unavailable.
A formal/numerical spectrum or AutoEFT field list need not identify an actual
mass radical. Such inputs may permit charge arithmetic without permitting a
physical exclusion.

Record the specific missing item: action compatibility, embedding, mass/index
transport, actual field dictionary, or theorem. Do not place all these gaps
into a single proposed proof task.

## What can be checked before constructing a mass

R1 is useful when the search specification itself fixes a commuting
ambient action, standard chain and desired light dual index. The theorem rules
out achieving that target by **any** admitted invariant mass; it does not
require first finding a mass that realizes it. One must still certify that the
candidate's UV action and physical embedding belong to this class.

Similarly, a mass-independent sector presentation can exclude every mass
when its pairing restrictions and constituent surplus are known. Scalar/block
phase identities can reject proposed charge fits before constructing a mass,
but promoting that rejection to a physical coefficient statement requires the
corresponding light-field admission.

If only the desired IR spectrum is specified, that is a target to test, not
an established spectrum of the input. If neither an exclusion implication nor
its applicability has been established, retain the input as undetermined.

## Decision labels and stopping rules

- **Excluded target:** a theorem proves the requested action/index target
  cannot be realized within the admitted input class.
- **B1 coefficient prohibition defeated:** a nonzero actual physical qque
  coefficient has been proved. This defeats total B1 prohibition but does not
  establish a generated interaction or proton decay.
- **Selected prohibition proved:** every coefficient in the specified actual
  domain is zero. For all B1, use the full selected-domain theorem; qque alone
  is insufficient. See the [prohibition catalogue](../prohibition-patterns/catalogue.md).
- **Undetermined:** hypotheses, connection or theorem are missing. This is
  neither exclusion nor evidence of protection.

Do not identify a neutral torus signature with a nonzero physical exterior
coefficient. Do not infer an actual radical from a UV character. Other
embeddings, noncommuting actions and unspecified light spectra are not
excluded merely because the standard-chain route is unavailable.

## Scope of further work and verification

A disjoint exploration-input classification has not been constructed. It must
include carrier, scalar representation and VEV data as well as action and
embedding. An executable applicability checker and new proofs for uncovered
cases have not been implemented. Route numbers alone do not define work
packages or support effort estimates without fixed inputs.
This map records existing theorem routes and their application boundaries.
No Lean source or dependency has changed; no Lean build is rerun for this
documentation-only inventory. Local links and whitespace are checked separately.
