# Full Vectorlike Light Spectrum

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

The [global entrance](../../../../../Physics/StandardModel/Operators/VectorlikeSpectrumQque.lean)
derives the three H-equivariant multiplicity decompositions formerly supplied
to [balanced species extensions](../../applications/Physics/BALANCED_SPECIES_EXTENSION.md).

## 2. Inputs and conclusion

### Inputs

- Actual finite-dimensional ambient/mass sources with radicals K and K0,
  sharing compact topological H but not necessarily the same ambient group.
- A compatible jointly continuous SM-cover x H action on K.
- On K0, an exact n > 0 left-chiral SM spectrum plus singlets, with the
  reference source's T-unitarity and two actual conjugations.
- A finite-dimensional jointly continuous SM-cover x H representation X and
  an actual SM-cover x H equivalence K = K0 + X + X.dual.

The reference has its compatible SM action; no independent reference
continuity premise is needed by this API. Masses are symmetric T x H
invariant forms, as before. They need not be zero if their actual radicals
meet the stated conditions. The decomposition is not inferred from arbitrary
UV matter or from SM particle counts alone. The dual includes H.

### Outputs

Compactness of the SM cover and continuity of X give first-factor
semisimplicity. The trace pairing on the two intertwiner spaces is proved
perfect for each concrete irreducible gauge species. This produces an
H-equivariant duality of multiplicities. Together with direct-sum transport,
it constructs each balanced-species certificate, then proves shared positive
support in the actual automatic normalized presentation and a nonzero qque
exterior coefficient on actual participating light fields with spinors.

No species-decomposition, semisimplicity, irrep-presentation, positive-support
or nonzero-coefficient certificate is added to the public endpoint. The full
spectrum equivalence remains an input; this is not an executable classifier.
The new source needs neither exact-SM content nor its own conjugators or
T-unitarity. The reference still supplies the structural constraints.

## 4. Proof structure

### Nonzero-Extra Control

The [SU(5) benchmark](../../../../../GUT/SU5/SelectionRules/VectorlikeBenchmark.lean)
uses two copies of 10 + bar5 and one dual copy, trivial H, and zero mass.
The actual representation, compatible action and global radical decomposition
are constructed. Its additional Q multiplicity is strictly positive, and
the radical cannot have an exact n-generation-SM-plus-singlets spectrum for
any n and s. Shared positive support and nonzero actual exterior qque are
proved for that source. This demonstrates application outside the older
exact-spectrum entrance; it does not establish realistic masses or dynamics.

No vacuum, Yukawa, anomaly, Wilson coefficient, amplitude or lifetime claim
is made. The general theorem applies to compact continuous non-Abelian H,
but this particular closed benchmark uses PUnit.

See [staged verification](../../../../topics/vectorlike-spectrum/README.md) and
[the implementation map](../../../../topics/vectorlike-spectrum/results.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
