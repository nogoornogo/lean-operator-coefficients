# Existing Interfaces And Pinned Sources

The original reuse candidates are listed below. Implemented component bridges
and remaining source inputs are distinguished in the [result](result.md) and
[conventions](conventions.md).

| Interface | Intended use and boundary |
| --- | --- |
| [BNV through seven dossier](../../proof/current/applications/Physics/BNV_SEVEN_COMPLETENESS.md) | Independent matter/Higgs sectors and completeness, not generation |
| [BnvSevenModelInterface](../../../Physics/StandardModel/Operators/BnvSevenModelInterface.lean) | Species-preserving actual-field transport; needs actual dictionaries |
| [BnvSevenSignedCoordinates](../../../Physics/StandardModel/Operators/BnvSevenSignedCoordinates.lean) | Signed exchange-constrained sector factors; identify correct support first |
| [PairedQuadraticElimination](../../../Math/LinearAlgebra/PairedQuadraticElimination.lean) | Algebraic stationary-field identity, check normalization and source types |
| [PairedVector](../../../Physics/FieldTheory/Matching/PairedVector.lean) | Existing spinor paired-vector consumer; scalar PS mediation is different |
| [SU5 TreeMatching](../../../GUT/SU5/Matching/TreeMatching.lean) | Example of ordered coefficient extraction, not a PS dependency or UV premise |
| [Previous PS study](../../model-studies/pati-salam-protection/results.md) | Frozen literature dictionary and exact nonzero epsilon control |

Proposed source locations: generic substitution/elimination in Math or Physics
by content, PS contraction and parameter consumer under `GUT/PatiSalam/`.
Register implemented sources/audits in the relevant aggregates. No filenames
or theorem names are assumed to exist before implementation.

## Literature Register

- [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/abs/2211.02054v2),
  [versioned PDF](https://arxiv.org/pdf/2211.02054v2): Sec.II Eqs.(10)–(14)
  (Yukawa and neutral mixing); Sec.III Eqs.(19)–(24) (higher contraction,
  diquark vertex, LEFT matching). Source of the candidate expressions and
  conditions; no conclusion is accepted as a custom axiom. Sec.IV rates and
  scale bounds are excluded.
- [Liao–Ma, 1607.07309](https://arxiv.org/abs/1607.07309): dimension-seven
  operator classification comparison only. Its RGE calculation is excluded.
- [Babu–Mohapatra, 1207.5771](https://arxiv.org/abs/1207.5771): SO(10)
  dimension-seven B-L-violating mechanisms motivate reuse; no SO(10) application
  or generation theorem is included here.

The pinned PS paper studies a possible baryon-violating mechanism; this topic
is not a proposed refutation of a claim of absolute proton stability. The
higher PS operator coefficient's own UV origin remains outside the endpoint.

- [Dolan–Dutka–Volkas, 2012.05976v2](https://arxiv.org/abs/2012.05976v2),
  [versioned PDF](https://arxiv.org/pdf/2012.05976v2), Eqs.(2.10),(2.15),(2.17):
  bounded predecessor convention check only. Its component-VEV convention
  differs from the pinned BNV paper's sqrt(2) definition; no automatic coupling
  conversion is established. The paper's phenomenological analysis is not used.
