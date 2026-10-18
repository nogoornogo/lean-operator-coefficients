# Literature on Yukawa Coupling Dimensions

Reviewed stage 01 on `proof/yukawa-full-space`, at checkpoint `checkpoint 01`.
This is a documentation milestone within the existing topic; its integration
target remains `master`, and the incomplete parent topic remains unmerged.

The mathematical ingredients for the proposed 22-dimensional coupling space
are established in the literature. No source directly stating the
17-dimensional evaluation kernel for this repository's scalar and vacuum was
located in the searches below. The calculation below is our deduction from
standard representation theory and the already proved evaluation image.
It is not a new Lean proof or an accepted external theorem parameter.

## Scope and search

The question concerns matter `15 + 2 bar6`, the 378-dimensional universal
symmetric-form scalar, zero bare mass and the specified fixed vacuum.
This is not a classification for an arbitrary conventional SU(6) Higgs sector.
The endpoint of this review is to identify references, application conditions
and two possible proof routes; adoption of a literature premise is left for
the user's decision.

Searches included SU(6), Yukawa, 378, 22, kernel, 17; SU(6) tensor products
15, 6, 84, 105; compact-group commutant multiplicities; and connected-group
versus Lie-algebra intertwining. These searches do not establish that no
direct model-specific publication exists. Related papers with different
scalar sectors cannot certify the present evaluation kernel.

## Sources and application conditions

1. R. Slansky, *Group theory for unified model building*, Physics Reports
   **79** (1981), 1-128,
   [DOI](https://doi.org/10.1016/0370-1573(81)90092-2),
   [university-hosted PDF](https://math.soimeme.org/~arunram/Teaching/RepThy2008/slansky.pdf).
   Tables 31 and 32 identify SU(6) irreducible representations and tensor
   products. Table 32 is on printed page 98 (PDF page 98).
   Conjugation and symmetric versus alternating summands matter; dimensions
   alone do not distinguish the two 105-dimensional representations.

2. Pavel Etingof, *Lie Groups and Lie Algebras*,
   [MIT course notes](https://ocw.mit.edu/courses/18-745-lie-groups-and-lie-algebras-i-fall-2020/mit18_745_f20_lec_full.pdf).
   Lemma 11.9 and Corollary 11.12 give Schur's lemma and the matrix-space
   description of Hom between completely reducible finite-dimensional complex
   representations (printed page 64, PDF page 62). Proposition 11.13 supplies
   complete reducibility for unitary representations.
   Corollary 11.2(ii), printed page 62 (PDF page 60), identifies group and
   differentiated Lie-algebra intertwiners for connected Lie groups.
   Applying the latter to the scripts additionally requires identifying the
   actual differentiated action and its complexification: the scripts use
   `sl6(C)`, whereas the real Lie algebra of SU(6) is `su6`.

3. Robert Zeier and Zoltan Zimboras, *On squares of representations of compact
   Lie algebras*, Journal of Mathematical Physics **56**, 081702 (2015),
   [arXiv 1504.07732v2](https://arxiv.org/abs/1504.07732v2),
   [DOI](https://doi.org/10.1063/1.4928410).
   The introduction explains computing commutants from generators and their
   relation to multiplicities. This supports the computational method;
   its tensor-square restriction results do not state our vacuum kernel value.

All three sources were consulted at stage 01. The earlier SageMath references
in the [topic record](README.md) remain software-method references.

## Deduction for the current scalar

Write `F = C^6`, `A = exteriorSquare F`, and `M = C^2` with trivial SU(6)
action. Then matter is `V = A + (F* tensor M)` and the scalar representation
is equivalent to `S = Sym^2(V*)`. In characteristic zero, expanding the
symmetric square and separating the symmetric and alternating factors gives

```text
S = Sym^2(A*)
  + (A* tensor F) tensor M
  + Sym^2(F) tensor Sym^2(M)
  + exteriorSquare(F) tensor exteriorSquare(M).
```

Using the SU(6) tensor-product decomposition, the first term has dimensions
105 + 15, the second has two copies of 6 + 84, and the final two terms have
three copies of 21 and one copy of 15. Our dual conventions give:

| Dynkin label | Dimension | Multiplicity in S |
|---|---:|---:|
| (0,0,0,2,0) | 105 | 1 |
| (0,1,0,0,0) | 15 | 2 |
| (0,0,0,0,1) | 6 | 2 |
| (1,0,0,1,0) | 84 | 2 |
| (2,0,0,0,0) | 21 | 3 |

These labels specify our synthesis and match the existing independent
character output; they are not a quotation of a model-specific theorem.
The dimensions total 378. Schur's lemma gives

```text
dim End_SU(6)(S) = 1^2 + 2^2 + 2^2 + 2^2 + 3^2 = 22.
```

Identifying Yukawas with this commutant, and using the fixed-vacuum evaluation
image of dimension 5 already proved in Lean, gives `dim ker evaluation = 17`.
The [coupling-kernel record](coupling-kernel.md) concerns this kernel of
couplings; it is distinct from the radical of a generated fermion mass,
whose dimension can also be 17 on some parameter strata.

## Decision between formalization and literature input

**Formalization route.** A reusable theorem deriving commutant dimensions
from a supplied decomposition and multiplicities would match the project's
general-purpose aim. The remaining model obligations are an equivariant
decomposition of the actual scalar, simplicity and nonisomorphism of its
summands. The existing `YukawaClassification.endomorphismEquiv` is an ordinary
equivalence; dimension transport also needs its linear structure verified.
This route can avoid the large row-reduction certificate, but finding standard
proofs in print does not make these Lean interfaces automatic.

**Literature-input route.** After an explicit decision, record the applied
decomposition or the resulting `finrank Couplings = 22` as a named theorem
parameter, with these references and model identifications. The existing
`CouplingEvaluation.dimension_twenty_two_iff` then yields kernel dimension 17
conditionally. An audit verifies that implication, not its literature premise.
A decomposition premise is more informative and reusable than merely assuming
the number 17. Neither premise has been added by this review.

Recommendation: if this model's numerical dimension is the only desired
endpoint, the literature-based derivation provides a reasonable explicit
boundary. If reusable formal mathematics is the priority, formalize the
general commutant formula first and treat the SU(6) decomposition as a separate
bounded obligation. The sources establish that the mathematical issue is
standard; the remaining cost is formal transport and completeness.

## Verification

Documentation only: local links and `git diff --check` checked. No Lean build
or axiom audit was rerun; the previous proof baseline is unchanged. No new
theorem premise, axiom, dependency or proof-completion claim was introduced.

## Existing Lean library search

Follow-up checked at stage 01. Sources were inspected at the dependency
revisions already fixed in `lake-manifest.json`: mathlib
`30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe` and TauCeti
`355c248fa848acd70c2a4b412ca5f53d37b0402a`. No dependency was installed or
updated. This search establishes API availability, not a new axiom audit
or successful model application.

### Immediately reusable results

Mathlib already provides
`Representation.IsIrreducible.finrank_intertwiningMap_self`, giving dimension
one over an algebraically closed field for a finite-dimensional irreducible
representation. The same file gives a subsingleton intertwiner space for
inequivalent irreducibles. These apply to arbitrary monoids, so they impose
no finite-group restriction on SU(6).
See [the pinned source](https://github.com/leanprover-community/mathlib4/blob/30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe/Mathlib/RepresentationTheory/Irreducible.lean).
`FDRep.finrank_hom_simple_simple` packages the dimension zero-or-one result
categorically in `Mathlib/RepresentationTheory/FDRep.lean`.
The finite-group character-sum formulas in `Character.lean` have additional
finite-group hypotheses and cannot be applied directly to SU(6).

Moreover, this repository's
[ExplicitMultiplicity](../../../Math/RepresentationTheory/Multiplicity/ExplicitMultiplicity.lean)
already proves `entry_off_diagonal`, `entry_diagonal_apply` and `apply_eq_mix`:
commuting operators on supplied pairwise inequivalent irreducible blocks are
matrices on the multiplicity indices. `operator_exhausts` and
`operator_commutes` establish the two directions for continuous operators.
Thus the main Schur argument should be reused. Packaging its algebraic linear
equivalence and extracting the sum-of-squares dimension formula remain
interfaces to verify; they need not start a fresh general theory.

### Additional TauCeti infrastructure

The pinned TauCeti contains actual tensor-square representation equivalences
(`Representation.tensorSquareEquivSymmetricExterior`), Weyl modules defined
by Young symmetrizers, and identification of the one-row and one-column
shapes with symmetric and exterior powers. Its
`centralizer_range_tensorPowerRep_eq_range_permTensorActionAlgHom` supplies
Schur-Weyl duality for the general linear group tensor-power action.
See [GeneralLinear](https://github.com/TauCetiProject/TauCeti/blob/355c248fa848acd70c2a4b412ca5f53d37b0402a/TauCeti/RepresentationTheory/Symmetric/TensorAction/GeneralLinear.lean)
and [ExtremeShape](https://github.com/TauCetiProject/TauCeti/blob/355c248fa848acd70c2a4b412ca5f53d37b0402a/TauCeti/RepresentationTheory/ClassicalGroups/ExtremeShape.lean).
These are useful ingredients, but a result for the full GL tensor power is
not already a decomposition of the present SU(6) symmetric-form scalar.

TauCeti also has
`ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap`
in [Intertwiner Dimension](https://github.com/TauCetiProject/TauCeti/blob/355c248fa848acd70c2a4b412ca5f53d37b0402a/TauCeti/RepresentationTheory/Compact/Intertwiner/Dimension.lean).
It counts continuous intertwiners using a Haar character integral for a compact
topological group and finite-dimensional continuous representations. This is
an alternative general tool; evaluating that integral as 22 for our scalar
still needs model-specific mathematics.

### Other external projects

The [Etingof representation theory formalization](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1)
contains Schur-Weyl work, including a source file named `Theorem5_22_1.lean`.
It is a candidate for further targeted inspection, not a verified dependency:
its imports, transitive axioms and compatibility with our pinned toolchain
have not been audited. The project README's completion claims do not replace
that audit. The [physlib project](https://github.com/leanprover-community/physlib)
was also searched as a physics-library lead. No directly reusable theorem
for this scalar's 22-dimensional commutant or 17-dimensional evaluation kernel
was located. Web discovery is not an exhaustive search of all Lean projects.

### Updated recommendation

Before introducing a literature premise, use the existing mathlib Schur API
and local multiplicity implementation to assess the remaining concrete
decomposition. The generic argument is largely available already. The next
bounded feasibility check should test whether TauCeti's tensor and symmetrizer
interfaces can supply the required SU(6) summands and their simplicity, or
whether a separate model proof is still needed. No full SU(6) decomposition,
Lie-to-group bridge or dimension 22 theorem has been established by this
library search. Documentation checks passed; no Lean build was rerun.
