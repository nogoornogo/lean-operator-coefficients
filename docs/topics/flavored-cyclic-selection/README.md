# Finite-Multiplicity Cyclic Residual Selection

- ID: `flavored-cyclic-selection`
- Status: completed
- Result type: exact finite-coordinate classification
- Working branch: `proof/flavored-cyclic-selection`
- Integration target: `master`
- Integration evidence: user-authorized master integration; Git ancestry records the merge

## Endpoint And Scope

Generalize one-generation residual selection to independent finite flavor
carriers with generation-dependent diagonal cyclic charges. Classify the
four dimension-six baryon-violating families and neutral-Higgs LLHH by exact
invariant coordinates, including repeated-field exchange relations. Prove
allowance/prohibition criteria and finite dimensions, and connect them to the
existing independently defined physical sectors.

The concrete residual group is `Multiplicative (ZMod N)` with `[NeZero N]`.
Flavor indices may be empty or have different cardinalities. No equal-generation
assumption, generic charge assignment or unrestricted neutral-tuple count is
silently imposed. Abstract arbitrary-H completeness remains unchanged.

## Deliverables And Acceptance

- Charge-diagonal representations and faithful neutral-weight coordinate rules.
- LLHH, DUQL, QQUE, DUUE and QQQL constrained coordinate classifications.
- Exact finite dimensions and necessary-and-sufficient nonzero criteria.
- Full signed four-family product and simultaneous LLHH selection criteria.
- Empty, singleton, trivial-charge and nonuniform-charge regression controls.
- Persistent strict audits, focused/full builds, dossiers and assumptions updates.

See [the frozen plan](plan.md). AutoEFT integration is explicitly postponed;
no generator installation or execution is required here.

## Work And Open Obligations

All six milestones are complete. QQQL's existing independent symmetric,
alternating and mixed dictionaries yield neutral coordinate cardinalities;
no new relation-matrix rank assumption is needed. No essential new physical
premise or large foundational prerequisite was encountered.

AutoEFT and general six-quark flavor selection remain deferred, not unfinished
obligations of this topic. Master integration was explicitly authorized by the user.

## Result And Verification

The full signed physical sector is linearly equivalent to the product of neutral
independent coordinates, with both inverses, total finrank and exact allowance/
prohibition criteria. LLHH gives neutral unordered pairs. Singleton scalar
criteria, empty carriers, unequal dimensions and nonuniform QQQL are certified.
See [results and verification](results.md) and the
[completed dossier](../../proof/current/applications/Physics/FLAVORED_CYCLIC_SELECTION.md).
Root README, dependency pins and literature coverage are unchanged.

## References

- [Plan](plan.md)
- [Results](results.md)
- [Scalar selection](../residual-selection-criteria/README.md)
- [Specified six-quark scalar selection](../delta-b-two-selection-criteria/README.md)
- [Coverage and limits](../../verification/li-basis-coverage.md)
- [Four-family completeness](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
- [Faithful cyclic character](../../../Math/RepresentationTheory/CyclicCharge.lean)
- [QQUE coordinates](../../../Physics/StandardModel/Operators/LiQqueCoordinates.lean)
