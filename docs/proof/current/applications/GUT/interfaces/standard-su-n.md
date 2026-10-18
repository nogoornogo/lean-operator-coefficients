# Standard SU(N) chain specialization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The standard block chain
gives a conditional selection-rule family for every N >= 5, with exact
rank-five/six comparisons and a rank-seven inhabitant.

### Original Status And Context

Dates, milestone labels and then-pending notes below are checkpoint context,
not a current project-wide status report.

Updated: stage 01

CHAIN-4 is **LEAN-CHECKED**. The [common theorem](standard-su5-chain.md)
now applies to the standard block chain for every N >= 5. This is a
conditional selection-rule theorem, not a classification of SU(N) models.

## 2. Inputs And Conclusion

The chosen standard chain, commuting Abelian residual action and exact
positive-profile dual radical target remain explicit.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Universal block inclusion pulls back the common SU(5) theorem; concrete
character calculations provide the rank-seven positive-target example.

### Compatibility And Positive Example

- N = 5: `rank_five_inclusion` is equality to the identity homomorphism;
  `rank_five_pullback` recovers the original actual SU(5) action.
- N = 6: `GUT.SU6.StandardSUNCompatibility.inclusion_eq` identifies the
  homomorphism exactly with the previous concrete block inclusion.
  `torus_eq` recovers its old physical (-2,3) torus. This comparison stays
  on the legacy side, so the new family does not import an SU(6) model.
- N = 7: `RankSevenBenchmark` constructs actual continuous unitary
  `Lambda^2(7) + 3 bar7`, of complex dimension 42. The residual group may
  be any Abelian group and acts trivially in this particular example.

The SU(7) character calculation comes from the defining matrix action,
its genuine dual and exterior-square functors, finite exterior bases, and
compact unitarization. On the standard SU(5) torus the checked identities are

```text
chi(Lambda^2(7)) = chi(10) + 2 chi(5) + 1
chi(bar7)       = chi(bar5) + 2
chi(source)    = chi(10) + 2 chi(5) + 3 chi(bar5) + 7.
```

Thus `restricted_index` agrees with the actual neutral `10 + bar5` model.
`hasTarget` proves the radical dual target for **any** invariant symmetric
mass on this source, using index conservation. `model` chooses zero mass;
`radical_finrank` proves it retains 42 zero modes, not just 15. The two
vectorlike pairs and seven neutral singlets are invisible to the dual
index. No extra-light-state exclusion is inferred. These are character
identities, not a new full-group branching equivalence theorem.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

### Universal Inclusion

`GUT.SUN.Block.inclusion m k` is the actual matrix homomorphism

```text
SU(m) -> SU(m+k), A |-> diag(A, I_k).
```

`rawMatrix_unitary`, `rawMatrix_det`, `matrixHom_unitary`, and
`matrixHom_det` prove the matrix conditions before the map is bundled.
`inclusion_injective` and `inclusion_continuous` hold for arbitrary natural
m and k, including an empty complementary block. `continuousInclusion`
bundles continuity; `inclusion_left` and `inclusion_right` identify its
actual entries. `exists_inclusion` covers any m <= n, and
`dimension_parameter` proves every N >= 5 is 5+k. The endpoint is indexed
by k to avoid dependent coordinate casts; no upper bound on k is assumed.

`GUT.SUN.StandardChain.Model k rho` is the existing common model at that
inclusion. `selection_rule_obstruction` applies uniformly, and
`continuousModel` supplies the inclusion's injectivity and continuity
automatically when the product action is jointly continuous. The common
scalar-family wrapper can use the same inclusion without a new mass theory.

The exact positive-profile **dual radical target**, strict commuting
Abelian residual action, and chosen standard SM -> SU(5) chain remain
explicit. The result produces supported neutral signatures, not a general
full-SM/Lorentz radical tensor, a coupling, amplitude, decay rate, or an
exact SM vacuum. Arbitrary embeddings and hypercharges are not covered.

### Modules And Audits

| Module under `GUT/` | Responsibility |
| --- | --- |
| `Math/LieGroups/SpecialUnitary/Block` | Arbitrary-rank block inclusion, determinant, unitarity, topology |
| `Math/LieGroups/SpecialUnitary/Matter` | Actual defining/dual/exterior actions and continuous unitary realizations |
| `Math/LinearAlgebra/ExteriorEigenbasisTrace` | Group-independent exterior eigenbasis and trace calculation |
| `SUN/Branching/DiagonalCharacter` | Actual diagonal traces and block-torus coordinates |
| `SUN/Branching/RankSeven` | Exact finite trace enumeration and rank-seven restriction identities |
| `SUN/SelectionRules/StandardChain` | Universal family endpoint and continuous wrapper |
| `SUN/SelectionRules/RankSevenBenchmark` | Constructed positive-target continuous source and radical dimension |
| `SU6/Embeddings/StandardSUNCompatibility` | Exact legacy rank-six comparison |

`Math/LieGroups/SpecialUnitary/Audit/AuditBlock` rejects transitive SU(5)/SU(6) imports in the generic
construction. `SUN/Audit/AuditStandardChain` rejects transitive SU(6)
imports, checks the endpoint and the actual positive SU(7) inhabitant,
and constructs a continuous Circle-residual model. The finite Z/3 audit
uses the neutral action, not a claim of nontrivial charge assignment.
`SU6/.../AuditStandardSUNCompatibility` retains the previous SU(6) model,
mass, and spectrum endpoints alongside the exact inclusion comparison.
All existing independent flipped and stronger retained-tensor results remain.

```sh
lake build GUT.SUN.Audit.AuditStandardChain \
  GUT.SU6.SelectionRules.Audit.AuditStandardSUNCompatibility
lake build
```

Verification: targeted 4279 jobs / 54 axiom-bearing reports; full 4437
jobs / 1666 reports. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. No dependency or toolchain revision changed. The concrete ranks
are compatibility/non-vacuity checks of the universal theorem, not sampling
evidence for its quantifier.

## 6. Scope And Limitations

Arbitrary embeddings, general hypercharges and exclusion of extra light states are not covered.

## 7. Sources And Verification

The [scope ledger](../../../inputs/GUT/ASSUMPTIONS.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
