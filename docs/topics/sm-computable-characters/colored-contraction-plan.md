# Positive color coupling by contraction diagrams

Resume base `checkpoint 01`, branch `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. This continues original endpoint 2
after the [actual signed Q core decompositions](colored-sixth-results.md).
It does not open a general classification of all compact-group representations.

## Candidate endpoint to prove

For a finite word of the reachable fixed color factors, replace scalar
allowance by existence of a finite contraction diagram. A vertex carries p
vector slots and q covector slots. The reachable vertices are symmetric powers,
the trace-free adjoint, the already constructed cubic/quartic contraction
kernels and their actual duals.

A diagram partitions all slots into vector/covector pairs and triples of
vectors or triples of covectors. A pair inside one trace-free vertex is
forbidden; a determinant triple may not use two slots from the same symmetric
vertex. Equivalently, use bounded nonnegative pair/triple incidence counts
with the prescribed vertex degrees. This is a positive finite combinatorial
condition, not an unknown Hom, signed coefficient, dimension or rank test.

This criterion is a **proof target**, not an imported theorem or a completed
classification. Both necessity and sufficiency must be connected to the
actual statistical sources before an all-content claim is made.

## Literature guidance, with no new theorem parameter

- Alexander Schrijver, [Tensor subalgebras and First Fundamental Theorems in
  invariant theory](https://arxiv.org/abs/math/0604240), section 5, derives the
  special-linear mixed tensor spanning statement from evaluation and the two
  volume tensors. Its hypotheses and tensor orientations must be instantiated;
  it is guidance for a Lean proof, not an accepted input.
- Sergey Fomin and Pavlo Pylyavskyy, [Webs on surfaces, rings of invariants,
  and clusters](https://pmc.ncbi.nlm.nih.gov/articles/PMC4103320/), section 1,
  records the evaluation/determinant generators for vectors and covectors.
  No cluster-algebra or web-basis completeness premise is required here.

The proposed restricted-vertex nonvanishing criterion and its conversion to
bounded incidence counts are the local argument to prove; neither paper is
being cited as already proving that exact repository statement.

## Checked library inputs and missing connections

The pinned TauCeti module
`RepresentationTheory.Symmetric.TensorAction.GeneralLinear` proves
`mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep` over an
infinite field with invertible factorial. Over complex numbers its hypotheses
hold symbolically. This is the available Schur-Weyl commutant theorem; it does
not itself identify compact SU3 invariants or the restricted color kernels.

The pinned
`LinearAlgebra.Matrix.SpecialLinearGroup.Transvection` proves
`Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`.
The local `SL2SymmetricSpan.coefficient_fixed_of_compact` already extends
compact SU2-invariant functionals on spanned modules to complex SL2. These
are the proposed compact-to-SL3 bridge through the three coordinate planes.

Existing canonical trace-kernel sections and symmetric-power maps give the
bounded restricted-factor embeddings/retractions. Mathlib polynomial extensionality
over an infinite field can supply a simultaneous nonzero specialization; no
large polynomial or tensor basis should be expanded.

## Proof sequence

1. Construct three complex SL2 planes in SL3, relate their compact parts to
   the existing actual SU3 planes, and use transvection generation. Prove
   symmetric-power spanning for the standard/dual plane restrictions and
   their arbitrary mixed tensor words. This must discharge compact invariance
   extension, not assume it at the endpoint.
2. Derive the mixed evaluation/volume spanning theorem from the pinned
   Schur-Weyl theorem. Use the existing determinant units to compare unequal
   vector/covector degrees with balanced endomorphisms. Triality exclusions
   are already available. Every semantic curry and split must be explicit.
3. Package the reachable actual color factors with their raw symmetric-slot
   embeddings/retractions, trace identities and pure flag vectors. Prove the
   corresponding facts for actual dual factors using the proved perfect pairings.
4. Construct invariant contractions and prove valid diagrams nonzero on flag
   vectors. A candidate affine chart uses v=(1,x,y), f=(-ux-y,u,1), so f(v)=0.
   Pairings between different vertices and determinants on three distinct
   vertices must be proved nonzero polynomials, then specialized simultaneously.
5. Prove invalid contractions vanish on the actual symmetric/trace-free
   images. The spanning theorem then proves necessity. Convert diagrams to
   finite bounded incidence data without enumerating content or rank tables.
6. Combine the actual core/generation decompositions, positive color criterion,
   joint SU2 coupling paths, Higgs cutoff and scalar q/l neutrality. Only the
   final all-content iff, with every input discharged, completes endpoint 2.

No `sorry`, custom axiom, new literature premise, audit exception, dependency
change, numerical certificate or raised proof limit is allowed. Counterexamples
must correct the candidate statement. Routine proof/verification checkpoints
continue; a genuinely new scope requirement must be recorded explicitly.

Stages 1 and 2 are now proved by actual maps on both mixed-color orientations;
see [results](colored-contraction-results.md) and
[verification](colored-contraction-verification.md). The generic split-source
support helper isolates stage 3 onward: a contraction must survive the actual
symmetric/trace-free embedding, then its nonvanishing must be converted to
the positive finite diagram condition. Those stages and the final consumer
remain obligations.

The [flag/vertex results](colored-flag-vertex-results.md) prove the positive
graph criterion on incident flags, actual symmetric retractions, single-pair
trace exclusions for the three reachable contraction kernels, and their
dual comparisons. The next semantic step identifies the spanning family
with diagrams on vertex slots. It is enough to use canonical diagrams with
q evaluation pairs and k majority-orientation determinant triples, indexed
by permutations at degree q+3k. This avoids introducing a separate invariant
web basis or general SU3 highest-weight theory. Degree/owner incidence can
be expressed as a finite permutation predicate; converting it to count data
is optional output, not a prerequisite for the support iff.

The [labelled-diagram result](colored-diagram-results.md) proves the actual
evaluation formulas and positive flag iff in both orientations, the adjoint
raw vertex and both local symmetric-slot identities. Next flatten grouped
vertices into raw vector/covector slots, factor invalid contractions through
the local zero traces or determinant/symmetry cancellation, and transport
valid flag witnesses. This semantic assembly remains to be proved before
combining color with the existing joint spin and q/l consumer.

For grouped-source assembly, use binary tensor trees, matching the existing
iterated species decomposition. A leaf has its own owner label (independent
copies must not share a label merely because their species agree). Flatten
each raw leaf of degrees (p,q), and combine nodes with the existing actual
mixed-power regrouping equivalence. Prove the arbitrary-slot generator law
and separate owner maps first; then transport local symmetry/trace exclusions
and flag witnesses through this same map. No new sigma-tensor foundation or
arbitrary chosen slot order is a theorem input.

The first tree consumer packages an actual raw split and its incident-flag
preimages at each leaf. This suffices to prove that every valid diagram
gives a nonzero actual coefficient on any such tensor tree. Necessity is
separate: the package must additionally carry the verified local symmetry
and trace exclusions, and those exclusions must be propagated to all
invalid diagrams before an iff or endpoint-2 completion is claimed.

The [actual tree construction](colored-tree-results.md) now proves raw
flattening, both spanning transports and positive/negative constructive
support for arbitrary trees of verified vertices, including the reachable
opposite/dual local models. Necessity still requires the global invalid-diagram
exclusion from local trace and symmetry, followed by the SM consumer.

## Invalid-diagram exclusion refinement

The next bounded step introduces the symmetric source tree with the same
leaf labels as the raw tree. Polarization proves that independent vector and
covector pure powers determine every linear form on it. The raw embedding
therefore kills any determinant using the same leaf twice, in either color
orientation. This is an equality of linear maps on the entire symmetric
source, not just a test on flags. Actual reachable vertices then factor through
that source using their already constructed normalized symmetric inclusions.

The second exclusion is an evaluation pair internal to one leaf. It must
factor through that leaf's trace, using permutation symmetry and the unique
use of each raw slot in a canonical contraction. The trace-zero condition
must be proved for each actual vertex and propagated through the tree. Do
not replace this condition by flag evaluation, or leave invalid-diagram
vanishing as an unexplained final premise. The stop gate and endpoint remain
the full actual support iff and the original q/l consumer; these two local
steps are intermediate verified milestones only.

The two exclusion rules and the complete pure-color word iff are now
proved; see [positive coupling results](colored-positive-coupling-results.md).
Every concrete local certificate is discharged, including opposite and
actual dual actions. The next obligation is the actual full-group
species/core and generation composition, retaining weak, independent-spin,
Higgs and q/l labels jointly. This color theorem alone does not close
original endpoint 2.
