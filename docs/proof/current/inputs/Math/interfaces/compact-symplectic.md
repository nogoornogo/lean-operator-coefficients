# Compact symplectic group and chirality

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. Actual compact symplectic
constructions give torus/inverse conjugacy and character-index obstructions,
including arbitrary subgroup restrictions.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Updated: stage 01

## 2. Inputs And Conclusion

The character applications use finite-dimensional sources; positive-target
exclusion retains a supplied faithful target evaluator.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Quaternionic eigenvector pairs give paired eigenbases, torus conjugacy and
inverse conjugacy; character conservation then gives the obstruction.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Declarations

All core declarations use namespace `GUT.CompactSymplectic`.

- [CompactGroup](../../../../../../Math/LieGroups/Symplectic/CompactGroup.lean): `Group`, closedness,
  compactness, matrix injectivity, and the continuous injective
  `toSpecialUnitary` map with determinant one.
- [Torus](../../../../../../Math/LieGroups/Symplectic/Torus.lean): `torusHom`, injectivity and continuity,
  actual `inversionElement`, and `torusHom_inverse_conjugate` for every n.
- [TorusCharacters](../../../../../../GUT/Sp/TorusCharacters.lean):
  `torus_character_eq_dual`, `torus_mass_zero_index`, and
  `torus_virtualCharacter_inv`, for arbitrary finite-dimensional sources.
- [UnitaryEmbedding](../../../../../../Math/LieGroups/Symplectic/UnitaryEmbedding.lean):
  `unitaryInclusion`, `specialUnitaryInclusion`, injectivity, continuity,
  and `specialUnitaryInclusion_diagonal`.
- [StandardChirality](../../../../../../GUT/Sp/StandardChirality.lean), subnamespace
  `StandardChirality`: `inclusion` for SU(5) -> USp(10) and `blockInclusion`
  for SU(5) -> USp(2(5+k)); actual torus factorizations and inverse equations;
  `not_model` and `not_block_model` exclude the positive exact light target
  in the existing model interface, without an assumed character equality.

See [the scope dossier](../../../applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md).

### SP-2 Declarations

- [QuaternionicStructure](../../../../../../Math/LieGroups/Symplectic/QuaternionicStructure.lean): the
  actual `defining` action and preserved Hermitian pairing;
  `quaternionicMap`, its matrix formula, square, equivariance, and the
  TauCeti `IsQuaternionicStructure` instance proof; orthogonality,
  independence, eigenvalue conjugation, and preservation of the pair's
  orthogonal complement.
- [EigenvectorPair](../../../../../../Math/LieGroups/Symplectic/EigenvectorPair.lean):
  `defining_eigen_norm`, `exists_eigenvector_pair` for every group element
  at positive rank, and `defining_preserves_orthogonal_pair`.

- [QuaternionicSpectral](../../../../../../Math/LinearAlgebra/Quaternion/QuaternionicSpectral.lean)
  and [QuaternionicEigenbasis](../../../../../../Math/LinearAlgebra/Quaternion/QuaternionicEigenbasis.lean),
  namespace `GUT.QuaternionicSpectral`: invariant subspace restriction,
  normalized eigenvectors, maximal paired frames, `Data.exists_paired_eigenbasis`,
  and `Data.finrank_eq_twice`. No concrete gauge group is imported.
- [PairedEigenbasis](../../../../../../Math/LieGroups/Symplectic/PairedEigenbasis.lean): `hilbertData` constructs
  all hypotheses from actual matrices; `exists_paired_eigenbasis` retains
  the canonical two-half indexing at exactly the original rank.
- [TorusConjugacy](../../../../../../Math/LieGroups/Symplectic/TorusConjugacy.lean):
  `basisMatrix_symplectic`, `exists_torus_conjugate`, and `inverse_conjugate`
  for every group element and every natural rank, including zero.
- [RestrictedCharacter](../../../../../../GUT/Sp/RestrictedCharacter.lean):
  `restricted_character_eq_dual`, `restricted_mass_zero_index`, and
  `virtualCharacter_inv`, with no conjugacy or self-duality certificate.
- [ChiralityObstruction](../../../../../../GUT/Sp/ChiralityObstruction.lean):
  `no_positive_SM_target` for any subgroup restriction and a supplied faithful
  target evaluator. No SU(5) chain is needed.
- `StandardChirality.not_arbitrary_model` excludes the existing model
  interface for every supplied SU(5) -> USp(2n) map. Old SP-1 endpoints remain.

## 6. Scope And Limitations

Zero chiral index does not imply an empty mass radical or an exact light spectrum.

## 7. Sources And Verification

The [scope dossier](../../../applications/GUT/COMPACT_SYMPLECTIC_CHIRALITY.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.

### Verification

[AuditTorus](../../../../../../GUT/Sp/Audit/AuditTorus.lean) checks compact/topological
group instances, rank zero, J squared and fourth power, the rank-one
non-involution, a torus element distinct from its inverse, and the actual
defining representation with zero mass and nonempty radical at zero index.
Its import guard rejects all SU(5)/SU(6) modules.

[AuditStandardChirality](../../../../../../GUT/Sp/Audit/AuditStandardChirality.lean)
checks the chosen-chain endpoints and exact k = 0 compatibility. It imports
the DUAL-2 controls for torsion charges, zero generations, singlets,
vectorlike pairs, and a non-self-dual actual SU(5) source; SU(6) imports
remain forbidden. Both audits are in the root build.

```sh
lake build GUT.Sp.Audit.AuditTorus GUT.Sp.Audit.AuditStandardChirality
lake build
```

SP-1 verification: targeted 3941 jobs / 118 axiom reports; full 4453 jobs /
1739 reports. All reported axioms are `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or new opaque assumption. Logs are regenerable
build artifacts, not source files. All-element conjugacy was not yet claimed
at that historical checkpoint; it is now checked below.

SP-2 first-pair verification:

```sh
lake build Math.LieGroups.Symplectic.Audit.AuditEigenvectorPair GUT.Sp.Audit.AuditTorus
lake build
```

Targeted 3355 jobs / 44 reports; full 4457 jobs / 1758 reports, with the
same standard axioms only. The
[eigenpair audit](../../../../../../Math/LieGroups/Symplectic/Audit/AuditEigenvectorPair.lean) is in the
root build, forbids SU(5)/SU(6) imports, and checks actual identity and
negative-identity matrices with repeated real eigenvalues, plus the
rank-zero failure of nonzero eigenvector existence. The torus audit now
reuses the shared actual defining representation instead of duplicating it.

SP-2 completion verification:

```sh
lake build Math.LinearAlgebra.Quaternion.Audit.AuditQuaternionicEigenbasis GUT.Sp.Audit.AuditTorusConjugacy GUT.Sp.Audit.AuditChiralityObstruction GUT.Sp.Audit.AuditStandardChirality
lake build
```

Targeted 3954 jobs / 168 reports; full 4466 jobs / 1789 reports, standard
axioms only. New persistent controls:

- [Abstract basis audit](../../../../../../Math/LinearAlgebra/Quaternion/Audit/AuditQuaternionicEigenbasis.lean):
  zero dimension, impossibility in complex dimension one, and no gauge imports.
- [Conjugacy audit](../../../../../../GUT/Sp/Audit/AuditTorusConjugacy.lean): an actual element
  outside the chosen torus, its inverse conjugacy, failure of a fixed J to
  invert all elements, and zero mass index on the full group. SU(5)/SU(6)
  imports are forbidden; earlier repeated-eigenvalue controls are retained.
- [Target audit](../../../../../../GUT/Sp/Audit/AuditChiralityObstruction.lean): arbitrary
  subgroup target exclusion, importing only the legacy pure SU(5) weight
  combinatorics, not any actual SU(5)/SU(6) source representation.

All are in the root build. No dependency upgrade, `sorryAx`, nonstandard
axiom, or unproved spectral/conjugacy certificate is used.
