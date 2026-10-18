# Checked Interfaces

## Mathematics

[IntertwinerTraceDuality](../../../Math/RepresentationTheory/Multiplicity/IntertwinerTraceDuality.lean)
uses trace(g composed with f) and semisimple splittings to prove a perfect
pairing on the two directions of intertwiner spaces for an irreducible R.
[MultiplicityDuality](../../../Math/RepresentationTheory/Multiplicity/MultiplicityDuality.lean)
combines transpose with this pairing and proves H equivariance:

```text
M(X.dual, R.dual) ~= M(X, R).dual.
```

The first-factor restriction of X is semisimple; no invariant pairing is
assumed as an extra certificate. Duality is algebraic complex-linear duality.

## Global Spectrum Entrance

[VectorlikeSpectrumQque](../../../Physics/StandardModel/Operators/VectorlikeSpectrumQque.lean)
retains the two actual source/mass interfaces and compact H from the balanced
extension. The new radical K has compatible continuous SM-cover x H action.
The reference K0 has exact n > 0 SM generations plus singlets, T-unitarity
and two conjugations. It takes a finite-dimensional continuous representation
X of SM-cover x H and ONE equivariant equivalence

```text
K ~= K0 + X + X.dual.
```

The continuous X action and compact SM cover imply first-factor semisimplicity.
Concrete gauge irreducibility, dual multiplicity equivalences, all three
balanced-species certificates, shared positive support of the automatic
presentation and actual nonzero exterior qque follow. The user does not
supply a multiplicity decomposition, irrep presentation, positive support
or nonzero coefficient. The new source needs no exact spectrum, T-unitarity
or conjugators of its own. Both masses may be nonzero if the stated radical
decomposition holds; the theorem does not construct such masses.

The global spectrum equivalence remains an input. SM-only vectorlike counts
are insufficient because the dual must include H. The construction is not
an executable decomposition algorithm or a classification of embeddings.
There is no Wilson coefficient, vacuum, Yukawa or decay-rate claim.

## Concrete Source

[VectorlikeBenchmark](../../../GUT/SU5/SelectionRules/VectorlikeBenchmark.lean)
constructs an actual SU(5) source from one retained 10 + bar5, a second copy,
and the dual of that second copy. H is PUnit with trivial action in this
concrete control; the general theorem above is not restricted to trivial H.
The source is put on a finite-basis Hilbert copy and has zero symmetric mass.
Its full radical, compatible continuous SM action and global spectrum
equivalence are constructed, not new premises.

`quark_extra_positive` proves the additional Q multiplicity is nonzero.
`not_exact` excludes the exact-SM-plus-singlets spectrum for every n and s.
`shared_positive` and `exists_actual_exterior` are closed theorems for this
source, using the new global entrance. Thus the extension is not just a
zero-extra recovery test. It supplies a formal example outside the old exact
entrance, not a realistic particle spectrum or a selected vacuum.
