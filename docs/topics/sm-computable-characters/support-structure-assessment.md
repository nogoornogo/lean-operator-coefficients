# Structural zero/nonzero multiplicity: literature and library assessment

Reviewed stage 01 on `proof/sm-computable-characters`, after `checkpoint 01`.
This is a research result and proposed proof route, not a new support theorem.
No dependency, theorem premise, numerical certificate or root README changed.

## Question and scope

The desired consumer is `Allowed(T)`, so deciding whether its local invariant
multiplicity is positive is sufficient. An exact rank or multiplicity numeral
is an optional stronger result. The existing
[support consumer](../../../Physics/StandardModel/Operators/SMSparseSupport.lean)
already separates this distinction. The external Weyl premise remains necessary
when identifying the existing extracted integer with the actual dimension.
A direct representation-theoretic support proof could instead reach the actual
Hom space first; it must prove that connection rather than assume it.

The 107 unresolved constant-species rows are 48 Q, 48 conjugate Q, 5 L and
6 conjugate L rows. They are not 107 arbitrary mixed contents. A uniform theorem
in the degree and weak highest weight for these families is a useful first
endpoint; it is not an all-mixed-content or 572-assignment classification.
The existing scalar q/l separation can be applied afterwards. It is not a
classification of other residual actions or nontrivial flavor actions.

## Literature that supplies the needed mathematical constructions

Work over complex finite-dimensional representations. In the formulas below,
`S_λ` denotes a Schur functor and `λᵗ` the transposed Young diagram.

1. **Exterior Cauchy decomposition / skew Howe duality:**

       Λⁿ(A ⊗ B) ≅ ⊕_{λ ⊢ n} S_λ(A) ⊗ S_{λᵗ}(B).

   For the proposed construction only the column component is needed:

       Λʳ(A) ⊗ Symʳ(B) ↪ Λʳ(A ⊗ B).

   [Pauly, *Strange duality revisited*, §3.2, equation (4)](https://math.univ-cotedazur.fr/u/pauly/SDR.pdf)
   states the finite-dimensional special-linear branching rule, citing
   Procesi, *Lie Groups: An Approach through Invariants and Representations*,
   Chapter 9, Theorem 8.4.1. This finite-dimensional statement is the relevant
   part, not the paper's affine/conformal-block theory.
   [Nazarov–Postnova–Scrimshaw, *Skew Howe duality and limit shapes of Young diagrams*](https://arxiv.org/abs/2111.12426)
   provides further context. Its complementary-diagram and dual-space
   conventions must not be substituted for the untwisted formula above
   without transporting the determinant twists.

2. **Symmetric Cauchy decomposition:**

       Symⁿ(A ⊗ B) ≅ ⊕_{λ ⊢ n} S_λ(A) ⊗ S_λ(B).

   The row component supplies `Symʳ(A) ⊗ Symʳ(B) ↪ Symʳ(A ⊗ B)`.
   [Achenjang's notes for Etingof's 18.755, Theorem 5.4, printed p.27](https://people.math.harvard.edu/~achenjang/assets/pdf/18_755_Notes.pdf)
   state and prove this decomposition via Schur–Weyl duality.

3. **Complementary exterior powers:** the perfect wedge pairing gives

       Λⁿ(V) ≅ (Λ^(D−n)(V))* ⊗ det(V),  D = dim V.

   The determinant line is essential. It is trivial on the special-unitary
   factors in the proposed application, but is generally nontrivial on U(1).
   The existing charge theorem must be reapplied separately. A vector-space
   duality alone does not supply an equivariant equivalence.

These constructions are established mathematics. The proposed SM specialization
and the adapters below are not yet Lean proofs. It should be cheaper to build
the two extreme Cauchy injections directly by symmetrization/antisymmetrization
than to formalize the full Schur-functor decomposition solely for this endpoint.
That is an implementation estimate to test, not a completed feasibility proof.

## Proposed degree-uniform Q and L support criteria

Let `W = ℂ²` be the weak doublet, `S = ℂ²` the active spin doublet,
`C = ℂ³` the color fundamental, and let the three-generation space have
trivial local action. Suppress U(1) and residual actions temporarily:

    V_Q = (C ⊗ W ⊗ S) ⊗ ℂ³,   dim V_Q = 36;
    V_L = (W ⊗ S) ⊗ ℂ³,       dim V_L = 12.

The candidate semisimple support statements are

    Hom(Symᵐ W, Λⁿ V_Q) ≠ 0 ↔
      n ≤ 36 ∧ 6 ∣ n ∧ 2 ∣ m ∧ m ≤ min(n,36−n),

    Hom(Symᵐ W, Λⁿ V_L) ≠ 0 ↔
      n ≤ 12 ∧ 2 ∣ n ∧ 2 ∣ m ∧ m ≤ min(n,12−n).

Here Hom is equivariant for color, weak and the independent spin factors;
the test representation `Symᵐ W` is trivial on color and spin. These are **proposed theorem
statements**, supported by the following mathematical proof construction.
They are not inferred as theorems from the CSV.

### Necessity

Color-center and spin-center actions force `3 ∣ n` and `2 ∣ n` for Q.
The spin center forces `2 ∣ n` for L. The weak center gives `n ≡ m mod 2`.
Capacity gives `n ≤ D`. The weak basis has equally many weights +1 and −1;
an n-element exterior basis subset has weight at most `min(n,D−n)`.
Consequently `Symᵐ W` cannot occur above that weight. The current weak bound
can be sharpened using these slot counts, or transported through complementary
exterior duality. Neither argument requires evaluating an extracted integer.

### Sufficiency by independent generation blocks

For one Q generation `U = C ⊗ W ⊗ S`, the two extreme Cauchy components give

    Sym⁶ W ↪ Λ⁶ U,
    Sym³ W ⊗ Sym³ S ↪ Λ³ U,

with trivial color action. In the first line, `Λ⁶(C ⊗ S)` is a trivial
determinant line for SU(3) × SU(2); in the second, `Λ³ C` is trivial.

- At n=6 use degree 3 in each of two different generations. Couple the
  two `Sym³ S` factors to spin zero. Clebsch–Gordan on the weak factors
  supplies every even m from 0 through 6.
- At n=12 use degrees 6+6 in two generations. `Sym⁶ W ⊗ Sym⁶ W` supplies
  every even m from 0 through 12.
- At n=18 use degrees 6+6+6. Iterated Clebsch–Gordan supplies every even
  m from 0 through 18.
- n=0 is the vacuum; n=24,30,36 follow from complementary exterior duality
  and self-duality of the SU(2) constituents.

For one L generation, use `Sym² W ↪ Λ²(W ⊗ S)` and the degree-one
`W ⊗ S`. Two degree-one blocks give m=0,2 at n=2. Two degree-two blocks
give m=0,2,4 at n=4; three give m=0,2,4,6 at n=6. Complementary degrees
give n=8,10,12.

Multiplication is used only between **different generation summands**, where
the graded exterior product decomposition gives an injection. Arbitrary
multiplication of fermionic coefficients is not asserted to be injective.
The source must be identified with these actual exterior representations,
including statistics, and the Hom direction must be transported correctly.

Reattach hypercharge using the repository convention:

| Single signed species | Required U(1) condition |
| --- | --- |
| Q | `n + 3δ = 0` |
| conjugate Q | `−n + 3δ = 0` |
| L | `−3n + 3δ = 0` |
| conjugate L | `3n + 3δ = 0` |

Conjugation exchanges the active spin factor and dualizes the gauge action;
the semisimple support conditions are unchanged after those transports.
For original Higgs degrees `(h,d)`, retain the existing constituent
`Admissible(h,d,m)` condition and `δ=h−d`. For the existing scalar q/l
actions, also retain total residual charge zero. None of these conditions
may be dropped in going from this local proposal to `Allowed(T)`.

As a diagnostic only, the proposed predicates agree with the signs of all
107 committed compiled multiplicities: 41 positive and 66 zero. This checks
the proposal against existing data; it is not its Lean proof or an independent
replacement for the construction above. In particular Q18,m6 would need only
a nonzero constituent from `Sym⁶ W` tensor cubed, not the integer 33573 or
the rank 63525913527.

## Lean availability at inspected revisions

Existing pins remain Lean `v4.35.0-rc3`, mathlib
`1a547d8a48a8fa7877d2decb69d7294723bb0187`, and TauCeti
`b9e2e182804073eb92718b68a9baf37df8e189bd`.

| Needed part | Existing source | Remaining connection |
| --- | --- | --- |
| Exterior products of independent summands | mathlib `ExteriorAlgebra.prodEquivTensor` and `prodEquivTensor_symm_apply_tmul_ιMulti` | Fixed multidegree injection, equivariance and three-generation adapter |
| Complementary degrees | mathlib `exteriorPower.wedgePairing` and `instIsPerfPairWedgePairing` | Equivariance, determinant character, restriction to actual sources |
| Trivial tensor determinant | mathlib `Matrix.det_kronecker` | Representation determinant/top-exterior adapter |
| SU(2) coupling and injectivity | Local [SU2ClebschGordan](../../../Math/RepresentationTheory/SU2ClebschGordan.lean), `embed_injective`, `equivalence` | Pullbacks/reassociation and finite coupling witnesses |
| Extreme Schur shapes | Pinned TauCeti `ClassicalGroups/ExtremeShape.lean`, `weylRepEquivSymPowerRep`, `weylRepEquivExtPowerRep` | Cauchy injection for tensor-product inputs; extreme-shape identification alone is insufficient |
| General Schur nonvanishing | Pinned TauCeti `WeylModule/Multiplicity.lean`, `nontrivial_intertwiningMap_iff` | Concerns Schur–Weyl multiplicity, not arbitrary SM singlet multiplicity |

The mathlib and local coupling names in the first four rows were checked with
`lake env lean`. The two exterior foundation declarations have only
`propext`, `Classical.choice`, `Quot.sound` as transitive axioms. TauCeti
candidate statements were source-inspected, not newly built or audited here.
Searches of the relevant pinned representation/Young-diagram files did not
identify a ready skew-Cauchy or general Kronecker-coefficient interface.
This is a search result, not proof of absence throughout Lean libraries.

### Newly found external library: Meta algebraic-combinatorics

[facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics/tree/b6022318e986a0c20764569208ba8ebbe1c04dbf)
at `b6022318e986a0c20764569208ba8ebbe1c04dbf` contains
`AlgebraicCombinatorics.littlewoodRichardson`,
`littlewoodRichardsonCoeff`, and `schurPoly_mul_expansion` in
[`SymmetricFunctions/LittlewoodRichardson.lean`](https://github.com/facebookresearch/algebraic-combinatorics/blob/b6022318e986a0c20764569208ba8ebbe1c04dbf/AlgebraicCombinatorics/SymmetricFunctions/LittlewoodRichardson.lean#L11702).
The theorem expands a product of Schur polynomials as a sum over tableaux;
it does not already identify branching of the actual SM representation.

Its three-file local import closure (`LittlewoodRichardson`,
`MonomialSymmetric`, `NPartition`, about 15,300 lines) was inspected, including
the endpoint bodies. A lexical screen excluding comments/strings found no
`sorry`, `axiom`, `native_decide`, `implemented_by` or `unsafe` token in that
closure. This is **not a compiled transitive axiom audit**. It imports the
whole upstream `Mathlib`; it has not been ported or compiled against our pins.
The package uses Lean v4.28.0 and mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Its root license is
CC BY-NC 4.0; adoption needs attribution/license review as well as compatibility
and proof audits. No source was copied into this repository.

ATLAS and LeanPool HEADs were rechecked via non-truncated GitHub recursive
inventories. They equal the previously
[inspected snapshots](../sm-rank-certificates/external-library-assessment.md):
ATLAS `8004bc185206d3d34cc6a7cf0840edca89cf64ce` and LeanPool
`01db1d7049cf9668bda1e9e106875ee1278b43e6`. The earlier finding remains
specific: inspected ATLAS v1 Weyl extraction candidates have `sorry`, whereas
LeanPool's relevant proved helpers are polynomial divided differences, not
a representation-theoretic character/positivity theorem. Inventory screening
did not identify a directly matching Cauchy/branching replacement.

## Why not start with general Littlewood–Richardson positivity?

LR tableaux give a positive combinatorial rule for tensoring polynomial
representations of one general linear group. Restricting a Schur functor to
a tensor-product subgroup, as needed for a generic Q source, instead introduces
Kronecker coefficients. The LR theorem alone does not close that problem.
Even saturation cannot be transferred indiscriminately:
[Briand–Orellana–Rosas](https://arxiv.org/abs/0810.3163) give counterexamples
to a strong saturation conjecture for Kronecker coefficients. This does not
establish hardness or impossibility for this fixed SM family.

For arbitrary mixed contents, a positive branching-witness theorem is still a
reasonable longer route, but its actual representation/statistics adapters and
the applicable branching rule must be specified first. General positivity of
an unevaluated character sum is not itself a decision criterion. The Q/L block
construction above avoids implementing that entire foundation for the 107 rows.

## Recommended bounded continuation and stop condition

1. First test one extreme Cauchy injection, its injectivity and equivariance
   on actual representations. Use existing tensor symmetrization and exterior
   maps; do not introduce the full Schur-functor theory as an implicit subtask.
2. Connect independent generation blocks, prove the lower-half Q/L nonzero
   statements with the existing CG theorem, and prove the center/weight zeros.
3. Transport complementary degrees with the determinant twist, then assemble
   the degree-uniform iff statements and existing q/l/Higgs consumers.
   Only after that consider arbitrary mixed contents as a separate endpoint.

The main uncertain cost is the equivariant extreme-Cauchy and exterior-duality
adapters, not big-integer arithmetic. Existing foundations make a bounded
attempt plausible; no elapsed-time or memory guarantee has been established.
If the first adapter needs a substantial new theory, stop with its exact
statement. A literature-input version may expose only the cited general
injection/duality as explicit theorem parameters, leaving the SM specialization
to prove; do not assume the desired Q/L positivity classification itself or add
a new premise silently. This assessment adds no such parameters.

## Verification of this assessment

- Read-only GitHub snapshots and full non-truncated inventories for the three
  external candidates; 58 files of algebraic-combinatorics were downloaded to
  temporary storage for configuration and candidate-source inspection.
- A temporary Lean probe imported `ExteriorPower.WedgePairing`,
  `ExteriorAlgebra.Product`, `Matrix.Kronecker`, and the local
  `SU2ClebschGordan`; the named checks and the two axiom prints above passed.
  The probe is reproducible with the following contents and `lake env lean`:

      import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
      import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
      import Mathlib.LinearAlgebra.Matrix.Kronecker
      import Math.RepresentationTheory.SU2ClebschGordan
      #check ExteriorAlgebra.prodEquivTensor
      #check ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti
      #check exteriorPower.wedgePairing
      #check exteriorPower.instIsPerfPairWedgePairing
      #check Matrix.det_kronecker
      #check Math.SU2ClebschGordan.embed_injective
      #check Math.SU2ClebschGordan.equivalence
      #print axioms exteriorPower.instIsPerfPairWedgePairing
      #print axioms ExteriorAlgebra.prodEquivTensor

- A temporary Python comparison against `neutral-sparse-results.csv` found
  zero sign mismatches for the proposed Q/L predicates. No table was changed.
- `node tools/docs/check-links.mjs`: 857 Markdown files, 5281 local inline
  links, 106 fragments, zero errors. `git diff --check` passed.
- No project Lean proof was edited, no new formal theorem was proved, and no
  full `lake build` or project strict-audit suite was rerun. This record does
  not replace the preceding kernel-certificate verification baseline.
