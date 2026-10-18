# Sufficiency, Necessity and Converse Inventory

## Reading rules

This is a source-inspected inventory, not a new theorem or an exhaustive
classification of all repository declarations. It covers the representative
prohibition routes, their concrete sector criteria, the input-side filters
and the current inverse construction. Existing iff statements retain their
original hypotheses. The O7 row now links its separately proved continuation;
the original inventory itself introduced no Lean theorem or verification baseline.

Three questions must stay separate:

1. Is prohibition equivalent to a condition on the actual coefficient domain?
2. Can that condition be computed from certified model inputs?
3. Can inputs satisfying it be realized by actual fields, masses and a vacuum?

An answer to one does not settle the others. A common constructed witness for
a necessary and a sufficient condition does not turn them into an iff.

## Existing exact criteria: reuse rather than reprove

| ID | Domain and hypotheses | Actual equivalence already proved | Remaining application work / evidence |
| --- | --- | --- | --- |
| E1 | Stable selected derivative-free mixed-field domain, supplied local/residual actions and finite species alphabet | Prohibition iff every selected actual residual-Hom factor is zero | Construct the field/action and support dictionary; no arbitrary Hom decision procedure. `Math.ProhibitionInput.factors_iff` in [ProhibitionInput](../../../Math/RepresentationTheory/ProhibitionInput.lean). |
| E2 | E1 with semisimple residual sources | Prohibition iff no selected source shares a simple constituent with the trivial target | Certify semisimplicity and the actual constituents. `no_shared_iff` in the same source. |
| E3 | Actual nontrivial carrier on which every group element acts by a scalar | Invariant-functional prohibition iff some element detects that scalar | Prove the scalar action after local/statistics quotients and nontriviality. `forbidden_iff_detect` in [ScalarProhibitionNecessity](../../../Math/RepresentationTheory/ScalarProhibitionNecessity.lean). |
| E4 | E3 with a standard cyclic character and positive cyclic order | Prohibition iff the total cyclic charge is nonzero | This is a factor/carrier criterion, not automatically all-B1. `cyclic_forbidden_iff` in [ProhibitionPatterns](../../../Math/RepresentationTheory/ProhibitionPatterns.lean). |
| E5 | Actual finite-dimensional light gauge/residual input; SM restriction and Q symmetric-square semisimplicity | Qque prohibition iff Sym² Q and uc tensor ec multiplicities share no simple constituent | Compute the actual product constituents and identify the full participating domain. `full_forbidden_iff` in [QqueCommonIrreducible](../../../Physics/StandardModel/Operators/QqueCommonIrreducible.lean). Compact variants retain topology/continuity premises. This is qque, not all-B1. |
| E6 | One-generation neutral-Higgs cyclic input; specified derivative-free dimension-six four-family sector | Prohibition iff all four family charges are nonzero | Already connected to the actual sector. With universal Yukawa charges this is 3q+l != 0. [CyclicResidualSelection](../../../Physics/StandardModel/Operators/CyclicResidualSelection.lean), [InverseCyclicSMCharges](../../../Physics/StandardModel/Operators/InverseCyclicSMCharges.lean). No all-degree converse follows. |
| E7 | Finite, possibly generation-dependent cyclic multiplicities in the same bounded sector | Prohibition iff all four typed neutral-coordinate index sets are empty | The generic iff is complete. Simplifying those actual sets to a small universal-charge predicate is an adapter problem. `forbidden_total_iff` in [FlavoredCyclicSelection](../../../Physics/StandardModel/Operators/FlavoredCyclicSelection.lean). |
| E8 | Specified one-copy scalar six-quark u²d⁴ domain | Prohibition iff 2u+4d != 0 modulo k; neutrality gives a two-coordinate coefficient space | Already complete for this domain. It is not all-degree B2. [DeltaBTwoCyclicSelection](../../../Physics/StandardModel/Operators/DeltaBTwoCyclicSelection.lean). |
| E9 | Specified one-copy LLHH domain with neutral Higgs | Prohibition iff the lepton's doubled cyclic charge is nonzero | Already complete; charged Higgs and other L2 contents have separate domains. `allowed_weinberg_iff` in CyclicResidualSelection and [WeinbergScalarFlavor](../../../Physics/StandardModel/Operators/WeinbergScalarFlavor.lean). |
| E10 | Prescribed actual B/W dipole selectors, finite-dimensional target flavor module | Selector allowance iff some residual intertwiner has a nonzero selected matrix element; family prohibition iff all selectors vanish | This is already an exact selected-domain criterion. It does not make distinct weights necessary. [DipoleFlavorSelection](../../../Physics/StandardModel/Operators/DipoleFlavorSelection.lean), [ComposableDipoleSelection](../../../Physics/StandardModel/Operators/ComposableDipoleSelection.lean). |
| E11 | Fixed actual domains and arbitrary selected target unions / mixed requests | Joint prohibition iff each requested domain is forbidden; allowance is required separately for each requested target | No new proof for every target combination. See [catalogue](../prohibition-patterns/catalogue.md). This packages predicates rather than classifying model parameters. |

These rows overlap. They are not distinct models, mutually exclusive input
classes or independent no-go claims. E6/E8/E9 can already be composed into
bounded simultaneous iff statements; extending their target names to every
operator would change the domain.

## One-way conditions: what the reverse would actually require

| ID | Condition and present conclusion | Reverse status at the same scope | Reason / exact missing item |
| --- | --- | --- | --- |
| O1 | Scalar charge detection on every selected content implies all-degree prohibition | A support-guarded all-degree converse is now proved; detecting all raw contents is not necessary | A neutral content may have zero local/statistics quotient, hence no coefficient. The [support-aware continuation](../prohibition-converse-boundaries/all-degree-results.md) proves the guarded iff and a neutral odd-fermion control. |
| O2 | A neutral admitted Q/uc/ec triplet gives a nonzero physical exterior coefficient; prohibition implies nonneutrality of every such triplet | Only necessity is proved by the current residual prefilter | Need the exact participating-domain zero criterion and its transport. The prefilter's HasCoefficient uses an exterior coefficient on the field sum, whereas intrinsic qque classification uses a species-degree submodule. Do not silently identify them or assume the whole exterior carrier is scalar. [ResidualQquePrefilter](../../../Physics/StandardModel/Operators/ResidualQquePrefilter.lean), [QqueCoefficientSector](../../../Physics/StandardModel/Operators/QqueCoefficientSector.lean). |
| O3 | Joint Q/uc/ec Hom surplus for a common irreducible guarantees a nonzero light qque coefficient for every admitted invariant mass | The proposed absence-of-surplus converse is refuted; surplus is not an exact coefficient criterion | Absence of this witness loses both actual mass-kernel information and product-constituent overlap. The [balanced-copy/zero-mass control](../prohibition-converse-boundaries/surplus-results.md) now certifies that failure on the actual participating physical domain. [SpeciesSurplusNecessity](../../../Physics/FieldTheory/Mass/SpeciesSurplusNecessity.lean). |
| O4 | Exact SM radical forces net copies (N,N,0,0) in the actual 10/bar5/40/50 family | Counts do not certify that a specified mass realizes SM; existence of some suitable mass is a different question | Balanced vectorlike copies can remain light for a chosen degenerate mass. The [existence continuation](../prohibition-converse-boundaries/copy-mass-results.md) now constructs some suitable mass iff the counts hold, with a zero-mass control refuting a claim about every chosen mass. [Full-family results](../theorem-driven-protection-constraints/full-family-results.md). |
| O5 | Equal-species characters, block compensation or standard-chain compatibility defeat a requested prohibition/target | Not a classification of every defeating action | Other actions may also allow coefficients. Use the full qque criterion for coefficient equivalence; retaining a target-index exclusion is appropriate for ambient-action routes. |
| O6 | Distinct weights force a prescribed LFV dipole selector to vanish | No unrestricted converse is asserted | Selected vanishing is evaluation on every actual intertwiner, not just weight mismatch. The [diagonal cyclic converse](../prohibition-converse-boundaries/lfv-results.md) now covers arbitrary vectors/functionals with coordinate support; arbitrary selectors and nonsemisimple actions require more information. E10 already gives the correct unrestricted evaluation criterion. |
| O7 | 3q+l != 0 for the three-generation bounded universal-charge BNV sector | Closed at the same scope: prohibition iff 3q+l != 0 | `three_generation_forbidden_iff` simplifies all four E7 coordinate sets; `three_generation_allowed_iff` certifies neutrality gives a nonzero coefficient. No new hypothesis. See [bounded converse](bounded-converse-results.md). |
| O8 | The selected lepton-parity construction proves all-degree B1 prohibition | The construction is one actual witness, not a necessary condition or classification of all 572 survivors | An all-degree charge characterization needs a neutral-content realization argument, including Lorentz/gauge/statistics and finite generation dimensions. Passing the degree-six filter does not supply it. [Construction result](results.md). |

Statements in the reverse-status column distinguish absence of a proof from
refutation. No new counterexample, converse theorem or general impossibility
claim is established by this document.

## Priorities and proposed proof contracts

### First: the three-generation bounded charge family (O7, now closed)

The user authorized this contract after the inventory. With the same positive
cyclic order, universal q/l actions, three generation indices, neutral Higgs
convention and actual dimension-six DeltaL=1 sector, Lean now proves

    bounded sector prohibition <-> 3q+l != 0 mod k.

All four typed coordinate index sets from E7 are empty when the common charge
is nonzero. Neutrality supplies a DUQL witness. Candidate membership is now
equivalent to this actual bounded prohibition, with no extra semisimplicity,
UV or mass assumption. The bounded endpoint is complete; it does not establish
an all-degree B1 iff. See [result and verification](bounded-converse-results.md).

### Second: a restricted LFV weight-selector converse (O6)

With finite cyclic diagonal flavor modules and normalized basis/projection
selectors, the implemented matrix unit proves selected allowance iff the
charges agree. Selected prohibition is equivalent to their differing.
This bounded O6 contract is complete; it is not an unrestricted converse to
forbidden_of_weights or a new assumption on arbitrary models. See the
[three follow-ups](three-followups-results.md).

### Third: the all-degree inverse family (O8)

Retain the current alphabet, three generations and cyclic action. First
identify neutral B1 contents not rejected by the Lorentz/gauge support
constraints. Then determine whether their actual coefficient carriers are
nonzero. Arithmetic neutrality alone is not that proof. If a neutral content
has no carrier, refine the condition rather than claiming a false converse.
Only after this bridge is explicit should a complete parameter classification
or a smaller finite criterion be attempted. No unproved uniform degree cutoff,
new derivatives/EOM/IBP framework or anomaly calculation is authorized by
this inventory.

O2 is useful after fixing the intrinsic qque/whole-exterior domain bridge.
O3/O4 should start with explicit refutation controls or a tightly bounded
existence question, not a promise that the numeric tests can become iff.
E1-E11 require usage/parameter adapters, not duplicate general theorems.

## Decision and verification

The original inventory recommended O7, which the user subsequently authorized
and which is now closed. The restricted O6 subclass is also complete; general LFV and the other
priorities retain their stated boundaries. Any subsequent contract must freeze its exact statement
before implementation. Public presentation remains a scoped
coefficient classification, not a quantum protection or UV-model theorem.

The original inventory was a documentation-only source inspection. The O7
continuation has its own proof builds and strict audits, recorded in
[verification](verification.md). Source inspection does not replace those checks.

The [four-stage continuation](../prohibition-converse-boundaries/results.md)
subsequently proved these guarded/adapted results and controls. It stops before
a general all-degree support classification or arbitrary nonabelian LFV
weight reduction; the earlier constructed witness and bounded tables are unchanged.
