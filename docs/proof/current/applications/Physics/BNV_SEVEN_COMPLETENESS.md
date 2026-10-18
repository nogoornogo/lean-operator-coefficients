# Matter/Higgs BNV Completeness Through Dimension Seven

## Result

`BnvSevenCompleteness.equiv` gives a complex-linear equivalence from the
independently defined `BnvMixedInput.bounded flavor scalarFlavor 7` to the
product of eight dimension-six residual factors and eight dimension-seven
exchange-constrained residual-Hom factors. All lower dimensions and both
baryon-number signs are included. `reconstruct_extract` and `extract_reconstruct`
prove both inverses. `forbidden_iff` and `nonzero_iff` give necessary-and-sufficient
total prohibition and existential allowance criteria.

Sources: [whole-space equivalence](../../../../../Physics/StandardModel/Operators/BnvSevenCompleteness.lean),
[signed dimension-six classification](../../../../../Physics/StandardModel/Operators/BnvSixResidualCompleteness.lean),
[signed dimension-seven classification](../../../../../Physics/StandardModel/Operators/BnvSevenSignedCoordinates.lean),
[strict audit](../../../../../Physics/StandardModel/Operators/Audit/AuditBnvSevenCompleteness.lean).

## Inputs And Citation Role

Inputs are an arbitrary abstract residual group R, complex modules and
representations for all ten signed SM fermion species and both scalar species.
Multiplicities need not be finite-dimensional. The Higgs doublet and its gauge
dual have explicit, possibly nontrivial residual actions. Opposite flavor/scalar
multiplicities are not identified by assumed conjugation or self-duality.
Gauge and Weyl actions, engineering weights and exterior/symmetric statistics
are fixed explicitly.

[Heeck–Le v2](https://arxiv.org/abs/2604.25134v2) supplies a field-content and
contraction comparison target, not an enumeration or completeness axiom.
See the [recovered source](../../../../topics/heeck-le-sector-comparison/source-recovery.md).
This is an independent extension, not a literal certificate for every printed
contraction or a verification of higher-dimensional reference tables.

## Proof Structure

Actual invariance derives hypercharge neutrality, color triality and Weyl
parity. Nonzero BNV pure values through seven occur only in degrees `(4,0)`
and `(4,1)`; all contributions below six vanish. The bounded degree equivalence
is two-sided and includes out-of-bound zero entries.

The scalar-free degree splits into lepton degrees +1 and -1, classified by
DUQL/QQUE/QQQL/DUUE and opposite-species factors. The
[signed field transport](../../../../../Physics/StandardModel/Operators/BnvSignedFieldTransport.lean)
reindexes independent multiplicities and transforms the gauge/Weyl group action.
It does not assume a semilinear involution on all model fields.

The single-Higgs degree splits into four positive and four negative supports.
Local invariant ranks are `2,2,1,2` for either sign. Proved local dictionaries,
typed field regrouping and statistics descent identify the factors with
residual tensor Hom submodules constrained by actual identical-field exchanges.
These are not free coordinates with exchange conditions omitted.

The [actual-field adapter](../../../../../Physics/StandardModel/Operators/BnvSevenModelInterface.lean)
constructs `sectorEquiv`, `boundedEquiv` and `residualEquiv` from species-preserving
equivariant fermion and scalar identifications. No coefficient-level completeness
premise is required. The dictionary must preserve species and engineering weights.

## Controls

[Finite cyclic controls](../../../../../Physics/StandardModel/Operators/BnvSevenControls.lean)
use Z/2 with one-dimensional multiplicities and residual-neutral scalars.
Quark parity forbids the entire bound-seven BNV space, using actual group
invariance and the derived odd quark count. With all charges neutral,
`positiveControl` reconstructs an explicit nonzero full-input coefficient from
a DUQL residual element; `positiveControl_ne_zero` proves its nonvanishing.

## Verification And Boundaries

The focused endpoint build passes (3,911 jobs). The persistent audit checks
26 endpoint declarations transitively alongside 173 earlier input/support/local
checks; only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Full `lake build` passes (6,484 jobs). Layout validation passes for 1,157 modules.
Local Markdown links and `git diff --check` pass. No dependency pins were changed.

Reproducible checks, run from the repository root with the pinned Lean/Lake
toolchain on PATH:

```sh
lake build Physics.StandardModel.Operators.Audit.AuditBnvSevenCompleteness
lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
git diff --check
```

The theorem covers derivative-free matter/Higgs BNV coefficients through seven,
not field strengths, derivatives, EOM/IBP, amplitudes or all SMEFT operators
without qualification. It proves coefficient existence, not UV generation,
anomaly consistency, quantum exactness or proton lifetime. No general decision
algorithm for arbitrary residual groups is claimed. Dimensions eight through
eleven remain unclassified at coefficient level; their individual extension
was explicitly not pursued when this topic closed at stage 01.
See the [topic record](../../../../topics/bnv-bounded-completeness/README.md).

## Related literature

[Lehman, *Extending the Standard Model Effective Field Theory with the Complete Set of Dimension-7 Operators*](https://arxiv.org/abs/1410.4193v2)
is operator-list context. Subsequently,
[Liao–Ma, *Renormalization Group Evolution of Dimension-seven Baryon- and Lepton-number-violating Operators*](https://arxiv.org/abs/1607.07309v2)
remove redundancies using EOM/Fierz identities and also calculate RGE. These
are different equivalence relations and physical tasks from the derivative-free
coefficient space above; no list count, EOM/IBP quotient or anomalous-dimension
result is imported or verified by this theorem. See the
[literature map](../../../RELATED_LITERATURE.md) for citation roles.
