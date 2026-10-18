# E6 Real Form and Global-Bridge Audit

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

**E6-0e is complete at the real Lie-algebra level, not the compact-group
level.** It closes item 2 of the [realization contract](../GUT/E6_MATRIX_PROTOTYPE.md),
after [E6-0d](E6_GECK_COMPARISON.md) closed item 1. No physical endpoint,
additional assumption, dependency revision, or group integration is added.

**Follow-up:** [E6-0f](E6_MATRIX_NORMALIZER.md) now proves the scalar
commutant and exact trace-zero Lie-normalizer bounds; it does not close
the global-group gate below.

## 4. Proof structure

### Checked Real Forms

Let `L` be an adjoint-stable complex matrix Lie algebra. Compact conjugation
is `sigma(X) = -X^H`. Its fixed points form a real Lie algebra `k`, consisting
exactly of the skew-Hermitian matrices in `L`. The new reusable
[MatrixCompactRealForm](../../../../../Math/LieGroups/Matrix/MatrixCompactRealForm.lean)
proves:

- paired adjoints on generators imply adjoint stability of their complex
  Lie span;
- `sigma` is conjugate-linear, involutive, and bracket-preserving;
- `Complex tensor[Real] k` is canonically **Lie-isomorphic** to `L`;
- `finrank Real k = finrank Complex L`;
- the real matrix action is injective and skew-Hermitian, and inclusions
  of adjoint-stable algebras restrict to injective real Lie maps.

The vector-space comparison reuses the pinned TauCeti
`LinearAlgebra/Complex/Conjugation.lean`: `realPointsEquiv` and
`finrank_realPoints`. The new proof checks the Lie bracket under scalar
extension, using mathlib's `Algebra/Lie/BaseChange.lean`.

[CompactRealForm](../../../../../Math/LieGroups/E6/Minuscule/CompactRealForm.lean) applies this
construction to the **actual**, previously verified matrix carriers:

| Declaration | Result |
| --- | --- |
| `matrixLieAlgebra_adjoint`, `d5MatrixLieAlgebra_adjoint` | Adjoint closure, derived from the pinned raising/lowering matrices |
| `compactRealForm_finrank`, `d5CompactRealForm_finrank` | Real dimensions 78 and 45 |
| `compactGeckEquiv`, `d5CompactGeckEquiv` | Complexifications are the actual scalar-extended E6/D5 Geck Lie algebras |
| `compactD5Inclusion`, `compactD5Inclusion_injective` | Actual injective real Lie inclusion on the same 27 coordinates |
| `compactGeckEquiv_inclusion` | Complexifying this inclusion gives precisely the previously checked numbered Geck D5 inclusion |
| `compactGeneratorElement` | All 18 previously checked compact generators inhabit this real form |
| `matrixLieAlgebra_trace` | Every element of the complex E6 matrix Lie algebra is traceless |
| `exp_compactRealForm_mem` | For every real-form element `X` and real `t`, `exp(t X)` belongs to actual SU(27) |

No comparison or dimension certificate is supplied as a hypothesis in the
concrete E6/D5 results. This real form is the full skew-Hermitian fixed
subalgebra; equality with the **real Lie span of the 18 displayed generators**
is not separately proved here and must not be assumed by a later construction.

### Pinned Global APIs: What They Do and Do Not Prove

These are source-inspection results at the pins in the
[feasibility dossier](../../../../topics/e6-global-topology/decisions/E6_FEASIBILITY.md), not a search of every possible
library or a compiled integration theorem.

| Pinned source | Available scope | Missing step for this project |
| --- | --- | --- |
| TauCeti `Geometry/Lie/Subgroup/LieAlgebra.lean` | For an already given finite-dimensional real Lie group, identifies the candidate Lie subalgebra of a closed subgroup by its one-parameter exponentials | Does not construct a Lie group integrating our matrix real form; the file explicitly defers the general immersed-subgroup theorem |
| `Subgroup/LimitCriterion.lean`, `Subgroup/LocalSeparation.lean` | Limit membership and local separation for closed subgroups | Inputs toward a closed-subgroup chart construction, not the complete compact E6 construction |
| `Geometry/Lie/Functor.lean` | Differentiates existing smooth group homomorphisms; naturality of exponential | Does not integrate a given Lie-algebra homomorphism |
| `Geometry/Lie/Faithfulness.lean` | Two smooth homomorphisms from a preconnected group agree if their differentials agree | **Uniqueness**, not existence of a group homomorphism, nor injectivity of a homomorphism with injective differential |
| `Algebra/Lie/E6/Minuscule/GroupScheme.lean` | Pinned algebraic matrix carrier, split torus and root subgroups | Its documentation explicitly excludes smoothness, reductivity, maximal torus and root-datum identification; it is not compact E6 |
| mathlib `Algebra/Lie/Derivation/Killing.lean` | `LieDerivation.IsKilling.exists_eq_ad`: derivations of the indicated finite-dimensional Killing algebra are inner | Useful for a prospective matrix-normalizer bound, not a global integration theorem |

In particular, exponentiation into SU(27) does not identify the subgroup
generated by these exponentials, its closure, its fundamental group, or its
center. A Lie inclusion does not settle a possible finite central kernel of
a later group map. The existing compact Spin(10) carrier has not yet been
compared with `d5CompactRealForm` as its differentiated Lie algebra.

## 6. Scope and limitations

### Follow-up Record and Cost Gate

**Current decision:** E6-0's feasibility phase is closed; additional
center/simple-connectedness/global construction is deferred. The
[endpoint-first plan](../../../../topics/e6-global-topology/plans/E6_ENDPOINT_PLAN.md) supersedes the sequence below.
These preserved proofs do not require completing their possible extensions.

The proposed **E6-0f** algebraic normalizer preflight is now
[completed](E6_MATRIX_NORMALIZER.md): distinct Cartan weights and checked
raising paths prove the scalar commutant, and the inner-derivation theorem
gives the trace-zero normalizer bound. **[E6-0g](E6_COMPACT_NORMALIZER.md)**
now constructs the closed compact matrix normalizer and proves its exact
all-time exponential criterion. **[E6-0h](E6_IDENTITY_COMPONENT.md)** now
passes it to the connected compact identity component and checks scalar
central elements of the full normalizer. **[E6-0i](E6_LOCAL_LOG.md)** now
proves local matrix-logarithm membership, component openness and exact
exponential generation. Subsequent **[E6-0n](E6_TANGENT_LIE_ALGEBRA.md)**
constructs local charts and a smooth Lie-group structure and identifies its
geometric tangent Lie algebra. The global-form extension is now deferred.

The motivation is to bound a prospective compact matrix carrier from above,
so that taking a closure cannot silently introduce extra infinitesimal
directions. These results still leave simple connectedness/global form,
order-three center, and actual compact
Spin inclusion to prove. A normalizer must not simply be renamed E6.

The historical estimate for the now-completed commutant/normalizer experiment
was 2-5 workdays, not an estimate for M2 or E6-1. If genuine Lie-group foundations are required,
retain the weeks-to-months review gate from E6-0; no reliable end-to-end
bound has been established. These are uncertain planning estimates, not
measured runtimes or credit commitments.

## 7. Sources and verification

### Verification

The persistent [audit](../../../../../Math/LieGroups/E6/Audit/AuditCompactRealForm.lean) checks
32 declarations against `propext`, `Classical.choice`, and `Quot.sound` only.
Concrete tests instantiate the real dimensions, complexifications,
compatible inclusion, and SU(27) exponentials without certificates. Negative
controls show that `E_0` is not skew-Hermitian and a compact generator is
nonzero. The targeted build passed (3820 jobs); all three new modules are
warning-free. Ten Python tooling tests also pass. The latest full regression
is recorded in [historical verified baseline](../../../../topics/proof-program-context/checkpoints/verified-baseline.md).

```sh
lake build Math.LieGroups.E6.Audit.AuditCompactRealForm
lake build
python3 -m unittest discover -s tools/e6 -p 'test_*.py'
```

The audit is imported by `GUT.lean`. Disposable logs are
`.lake/e6-0e-audit.log` and `.lake/e6-0e-full-build.log`; reproducible Lean
sources and this record are tracked.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
