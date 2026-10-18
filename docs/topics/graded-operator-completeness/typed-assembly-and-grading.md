# Typed Assembly And Grading Foundations

## Proved Interfaces

`MixedPatternAssembly.equiv` identifies actual invariant mixed coefficients
supported on a specified species-pattern orbit with typed ordered multilinear
maps satisfying invariance, fermion signs and boson symmetry. Normalized
alternation/symmetrization supplies reconstruction; restriction and reconstruction
are inverse. The fermion and boson degrees are arbitrary natural numbers,
including zero. Only species alphabets are finite; field modules may be infinite.

`TypedMixedTensorHom.equiv` connects invariant ordered maps to invariant
functionals on the heterogeneous ordered fermion/boson tensor carrier. This
interface does not impose exchange constraints: those remain a separate step.

`IndexedTensorSeparation.representationEquiv` regroups a finite heterogeneous
family of local/flavor tensor factors into the tensor of all local factors and
all flavor factors. `equiv_pure` gives the generator formula and `equiv_unique`
fixes the map canonically. The proof internally chooses bases of complex modules;
no chosen basis, finite dimension or contraction dictionary is a theorem input.
After replacing expensive definitional unfolding with named basis formulas,
the proof checks with the default heartbeat limit.

`PositiveContentGrading.bounded_finite` proves finiteness of content vectors
under any engineering bound when every species weight is strictly positive.
The charge-restricted subset is also finite. This does not prove gauge neutrality
from charge arithmetic, or construct a finite cutoff for all-degree prohibition.

`DirectSumFunctionalProduct.equiv` identifies invariant functionals on an
arbitrary direct sum of representations with the **product** of component Hom
spaces. Its zero, prohibition and nonzero iff theorems hold without a finite
index set. They do not identify this product with finitely supported coefficients.

## Remaining Connection

These are foundations, not the full frozen endpoint. The following remain:

1. Connect typed exchange constraints through heterogeneous regrouping and local
   descent to the constructed residual carrier `Q_c` for every field content.
2. Assemble content-orbit factors with weight/charge support, and derive the
   physical bounded/all-degree criteria through those proven equivalences.
3. Instantiate the signed SM/Higgs inputs and prove commuting comparisons with
   existing six/seven-dimensional classifications and their controls.
4. Add final connected regression/audit coverage and the completed-result dossier.

The coefficient-space decomposition theorem must not be declared complete by composing maps whose
exchange compatibility or content support has only been assumed. No AutoEFT,
external basis output, new dependency or dimension-eight-to-eleven enumeration
has been introduced.

## Sources

Verification: focused audit 3,191 jobs / 23 strict transitive checks; full build
6,503 jobs; layout 1,176 modules; 450 Markdown files / 2,997 local links, zero
errors; `git diff --check` passes. Only standard Lean axioms are accepted.

- [Typed mixed assembly](../../../Math/RepresentationTheory/MixedPatternAssembly.lean)
- [Typed ordered tensor Hom](../../../Math/RepresentationTheory/TypedMixedTensorHom.lean)
- [Canonical tensor separation](../../../Math/RepresentationTheory/IndexedTensorSeparation.lean)
- [Positive content grading](../../../Math/RepresentationTheory/PositiveContentGrading.lean)
- [Direct-sum functional product](../../../Math/RepresentationTheory/DirectSumFunctionalProduct.lean)
- [Strict audit](../../../Math/RepresentationTheory/Audit/AuditGradedOperatorFoundations.lean)
