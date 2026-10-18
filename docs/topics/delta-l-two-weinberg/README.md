# Delta-L = 2 Weinberg coefficient completeness

- ID: `delta-l-two-weinberg`
- Status: completed
- Result type: proved (bounded coefficient completeness and specified-VEV evaluation)
- Working branch: `proof/delta-l-two-weinberg`
- Integration target: `master`
- Integration evidence: merged into `master` by `checkpoint 01` after explicit authorization;
  see [verification](verification.md).

## Endpoint and scope

Classify the independently defined derivative-free `LLHH` coefficient sector,
then evaluate it at a specified Higgs VEV to obtain a Majorana mass coefficient.
Here `L` is a left-handed lepton doublet and `H` is the Higgs field; write `R`
for the residual symmetry group to avoid confusing it with the Higgs.
The first endpoint has one Higgs doublet with trivial residual action, an
arbitrary group `R`, and a complex lepton multiplicity representation `F`.
The proof needs no finite-dimensionality, compactness, continuity or self-duality.

The proved classification is a complex-linear equivalence

```text
WeinbergSector(F) ≃ₗ[ℂ] Hom_R(Sym² F, trivial ℂ).
```

Define the left side before constructing contractions: invariant scalar-valued
linear maps on `Λ² LeptonModel ⊗ Sym² HiggsModel`, for the supplied SM gauge,
Lorentz and residual actions. Equivalently, use multilinear maps alternating
in the two lepton slots and symmetric in the two Higgs slots, with a proved
equivalence between the interfaces. Do not put all four slots in an exterior
power or define the sector to be the image of the proposed basis.

Assign lepton degree one to `L` and zero to the Higgs, and baryon degree zero
to both. Prove the sector has `(ΔB, ΔL) = (0, 2)` in this convention; conjugation
reverses the lepton degree. Lepton grading labels the violating operator and
is not an extra invariance requirement. Include gauge hypercharge cancellation.

Model authors supply equivariant identifications of participating actual fields
with these standard models. The theorem does not discover fields, light spectra,
residual groups or vacua from a UV theory.

## Milestones and acceptance

1. **Freeze interfaces and test feasibility.** Fix field order, charge conventions,
   the independent mixed-statistics sector, and normalized evaluation probes.
   Check the two-left-spinor invariant line and the weak contraction space after
   Higgs-slot symmetrization. Existing four-spinor uniqueness is not itself a
   theorem about this two-spinor space.
2. **Prove reusable algebraic descent.** Connect mixed alternating/symmetric
   multilinear maps to the exterior/symmetric tensor domain. Prove equivariant
   transport and extensionality. Reuse symmetric-square descent rather than
   starting a general graded-algebra framework.
3. **Prove coefficient completeness.** Construct the explicit weak/Lorentz
   contraction, prove invariance and exchange laws, and extract its flavor
   coefficient from every invariant input. Derive flavor symmetry and residual
   equivariance. Prove assembly/extraction are linear and mutually inverse;
   an invariant contraction alone does not establish completeness.
4. **Expose actual-field and nonzero interfaces.** Transport the equivalence
   through a qque-style `Inputs` package. Prove existence of a nonzero sector
   coefficient iff the residual Hom is nontrivial. For trivial residual action
   and one-dimensional flavor, prove an equivalence with `ℂ` and dimension one.
   Test zero flavor and a one-dimensional residual character: the latter should
   allow a coefficient precisely when its square is trivial, including a
   nontrivial order-two character.
5. **Connect a specified VEV to Majorana mass.** Separate the antisymmetric
   Lorentz epsilon from the symmetric internal mass form. Prove the exact
   normalization of Higgs evaluation and restriction to a supplied neutrino
   embedding. In a fixed weak basis with VEV `(0,v)`, establish the coefficient
   formula as the explicitly normalized multiple of `v² κ`; do not guess the
   combinatorial factor. Prove the resulting map on invariant symmetric flavor
   forms is a linear equivalence for `v ≠ 0`, and is zero for `v = 0`.
   State the remaining symmetry after the VEV rather than asserting invariance
   under the broken electroweak group.
6. **Review and verify.** Register sources and persistent strict transitive axiom
   audits in the appropriate aggregates. Run focused builds, the audits, full
   `lake build`, layout/link checks and `git diff --check`. Review both inverse
   identities, actual-field assumptions, normalization and all nonzero claims.
   Commit verified milestones on the subsequently authorized topic branch;
   completion does not authorize merging.

Milestones 1–4 are the coefficient-completeness endpoint. Milestone 5 is a
separate consumer theorem, not a premise of completeness. Neither result
asserts a nonzero UV-generated coupling or nondegeneracy of an arbitrary mass
matrix. The general B/L parity selection rule is not a prerequisite.

## Feasibility and stop gate

Use one feasibility pass over at most two routes: (A) tensor invariant-factor
extraction followed by universal-property descent; (B) general multilinear
expansion with small exact weak/spinor coordinate lemmas, followed by the same
descent. Keep mathematical reduction separate from finite arithmetic and avoid
large generated lists of coordinate-specific elimination proofs.

The main uncertainties are the mixed-statistics interface and invariant-factor
extraction, not the construction of one contraction. If both routes require
new general invariant theory or graded-algebra foundations, record the missing
theorem and request a scope decision. Do not assume a spanning theorem as an
input, weaken the independent sector to the contraction image, or change pins.

Exclude multiple Higgs species, nontrivial residual Higgs representations,
derivative/higher-dimensional sectors, all-sector ΔL=2 classification, seesaw
matching, potential minimization, RGE, numerical masses/mixing and decay rates.
These require separate topics. The present plan is algebraic, not phenomenology.

## Implementation and result

- [Symmetric-square descent](../../../Math/RepresentationTheory/SymmetricSquareDescent.lean)
  supplies the symmetric multilinear-to-Hom interface.
- [Weyl pair invariants](../../../Physics/FieldTheory/Spinor/WeylPairInvariant.lean)
  prove the normalized two-left-spinor invariant line.
- [Qque completeness](../qque-coefficient-completeness/README.md) and
  [six-quark model inputs](../delta-b-two-model-interface/README.md) supply
  design precedents for independent sectors, probes and actual-field transport.
- [Majorana evaluation](../../../Physics/StandardModel/Operators/WeinbergMajorana.lean)
  uses the symmetric Higgs square directly and constructs the existing
  `InvariantWeylMass.SymmetricMass`. It does not invoke the scalar-linear
  Yukawa evaluation API or claim a separate bridge to that API.
- [Order-two Weyl mass example](../../../Physics/FieldTheory/Mass/WeylMassTwoTorsion.lean)
  is a regression against falsely excluding Majorana mass by a nontrivial
  residual character alone.

Route A is viable for the local factors: the existing symmetric-square/triplet
equivalence and exhaustive triplet contraction give weak uniqueness directly.
The two-left Weyl invariant line follows by restriction to SU(2). Mixed descent
uses existing universal properties, without new graded-algebra foundations.
The combined exchange law, physical field-order sector, SM hypercharge
cancellation and actual-field transport are proved. No coordinate-elimination
case lists or increased heartbeat settings were needed.

## Result and verification

All six milestones above are complete. The primary public interface is
[WeinbergSMInterface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean):
`homEquiv`, `onFieldsEquiv`, `exists_nonzero_iff`, `oneGenerationEquiv`,
`majoranaEquiv`, `mass_evaluation` and `mass_nonzero_iff`.

See [results and boundaries](results.md) and [verification](verification.md).
Foundation checkpoint: `checkpoint 02`; subsequent completion is recorded in this
branch's history. No proof obligations remain within this bounded endpoint.

The bounded endpoint is integrated. Input-interface unification is deferred by
user decision until the other planned operator topics (including ΔL=1) have
been addressed; the existing interface remains unchanged.
