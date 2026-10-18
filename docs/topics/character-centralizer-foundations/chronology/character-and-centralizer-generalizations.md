# Character and centralizer generalizations

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

- Completed generalization milestone A: the mathlib-only
  `CharacterRestriction` module proves conjugation-induced restriction
  invariance and non-invariant-target exclusion for arbitrary groups and
  finite-dimensional representations over arbitrary fields. Finite integer
  coefficients use `Finsupp`, including a version indexed by all `FDRep`
  objects. A faithful target evaluator suffices without any source polynomial
  model. Existing SU(6) finite presentations have a proved character-preserving
  adapter; actual/virtual `swap36` invariance and normalized no-uplift now use
  the generic API with their theorem statements preserved. Persistent audits
  include a three-point permutation-group obstruction, a signed realizable
  character, a noninjective parameter map, and a counterexample when evaluator
  faithfulness is dropped. Audited declarations use only standard axioms;
  full build 4230 jobs. The scoped physical endpoint is unchanged. B (algebraic
  kernel/cokernel character index) is next, then C (multiplicity commutants
  followed by unitary centralizers and topology); no dependencies were updated.
- Completed generalization milestone B: `CharacterExact` proves exact-sequence
  character additivity and the kernel-minus-quotient-cokernel index for
  finite-dimensional representations over any field of any monoid. The
  proof uses the pinned TauCeti exact-trace theorem, with no semisimplicity,
  unitarity, or invariant-complement assumption. An actual equivariant
  equivalence identifies the old orthogonal-complement model with the
  quotient and connects existing mass-index consumers to the algebraic
  proof. Symmetric-mass dual-character conservation also drops all norm,
  inner-product, and unitary-action hypotheses, using massive-quotient
  self-duality. Existing theorem signatures remain as compatibility wrappers.
  The persistent rational shear audit proves the absence of an equivariant
  section while checking indices +1 and -1; the older two-torsion mass audit
  remains checked. Audited declarations use only standard axioms; targeted
  audits and the full build passed (4234 jobs). No dependency versions or
  physical no-go assumptions changed. C is next. See the
  [exact-character dossier](../../../proof/current/inputs/Math/CHARACTER_EXACT.md).
- Completed the algebraic and coordinate stages of generalization C, not
  the full unitary-centralizer generalization. `MultiplicityCommutant`
  constructs models on actual isotypic components, proves intrinsic copy
  counts and the sum-of-squares dimension, and uses mathlib to identify
  semisimple intertwiner algebras with products of full matrix algebras.
  `CommutantCentralizer` identifies the actual GL centralizer with their
  units; the acting algebra itself need not be semisimple. The old unitary
  orthogonal-complement proof was extracted to `UnitaryMultiplicity`, with
  compatible SU(6) aliases/wrappers, supplying models for arbitrary
  finite-dimensional complex unitary group representations.
  `MultiplicityMatrix` checks the unitary block action, the determinant
  product with constituent-dimension exponents, continuity, and the closed
  weighted determinant kernel. Persistent audits cover repeated constituents
  with noncommuting endomorphisms, the zero representation, and an exactly
  two-element weighted SU kernel. Standard axioms only; targeted audit
  2961 jobs, full build 4242 jobs. A single mass-index proof now explicitly
  identifies its orthogonal-subspace type after the extraction; old theorem
  signatures, dependencies, and physical scope are preserved. Still open:
  an isometric multiplicity decomposition and its adjoint/determinant
  compatibility, then full actual U/SU topological centralizer equivalences.
  See the [multiplicity-centralizer dossier](../../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md).
- Completed the isometric-decomposition and topological-transport milestone
  of generalization C. `UnitaryIntertwiner` uses pinned mathlib's positive
  square root and commutation theorem to replace any algebraic equivalence
  between finite-dimensional unitary representations by an equivariant
  isometry. `IsometricMultiplicity` constructs Hilbert multiplicity
  coordinates with inherited constituent inner products, positive actual
  constituent dimensions, and the total dimension formula.
  `UnitaryCentralizerTransport` gives two-sided continuous conjugation
  equivalences of the actual U/SU centralizers and proves preservation of
  operator determinants. These are applied to the constructed Hilbert model;
  the targets are not yet products of multiplicity unitary matrix groups.
  The remaining bridge identifies the Hilbert commutant with amplified
  matrices, including adjoints and weighted determinants, and composes the
  final matrix-coordinate topological equivalences.
  Persistent audits include non-isometric input, zero and repeated trivial
  constituents, a proved nontrivial permutation action, and topological
  group instances. Standard axioms only; targeted audit 3088 jobs, full
  build 4249 jobs. No dependency revisions, previous proofs, or physical
  assumptions changed. See the
  [multiplicity-centralizer dossier](../../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md).
- Completed the final U/SU stage of generalization C. The actual Hilbert
  scalar-mixing action is faithful, preserves adjoints, and exhausts the
  intertwiner algebra by the already proved dimension comparison.
  Actual basis coordinates identify its determinant with the product of
  multiplicity determinants raised to actual constituent dimensions.
  `MultiplicityUnitaryCentralizer` and `MultiplicitySpecialCentralizer`
  compose with isometric transport to give two-sided continuous
  classifications by `product U(m_c)` and its full weighted determinant
  kernel. `UnitaryMultiplicityClassification` constructs all source data
  from the representation and unitarity proof alone. No compactness,
  connectedness, or independent classification certificate is assumed.
  The new persistent audit includes zero/repeated constituents, a
  nontrivial permutation action, continuity in both directions, and a
  nonidentity Hilbert operator of determinant one that an unweighted
  constraint would wrongly discard. The existing finite-kernel audit is
  preserved. A-C of the reusable generalization review are now complete;
  the scoped physical theorem and dependency revisions are unchanged.
  Targeted audit: 3606 jobs; full build: 4255 jobs. All newly audited
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
  See the [multiplicity-centralizer dossier](../../../proof/current/inputs/Math/MULTIPLICITY_CENTRALIZER.md)
  and the build record in [COMPLETED.md](../../proof-program-context/checkpoints/verified-baseline.md).
- Created annotated local preservation tags before standard-chain work:
  `mass-profile-complete-stage 01` at `checkpoint 01` and
  `representation-generalizations-complete-stage 01` at `checkpoint 02`.
  The latter marks reusable A-C generalizations, not the original physical
  lemma labels. No tags or commits were pushed. The plan was committed as
  `checkpoint 03` before proof edits.
