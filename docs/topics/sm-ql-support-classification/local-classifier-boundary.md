# Local Invariant Classifier: Two-Route Assessment

## The missing interface

The residual separation lemma targets

    Allowed(T(q,l,p,m,delta)) iff
      totalSignedCharge(q,l,p)=0 and LocalSupport(p,m,delta).

`LocalSupport` must eventually be an explicit predicate with no remaining
invariant-Hom `Allowed` term. All three flavor copies, color, weak,
hypercharge, left/right Weyl factors and exterior-statistical relations must
remain connected to the actual coefficient space. This is additional to the
already proved finite Higgs table and to the scalar-residual separation.

Two local construction routes were inspected once. Neither assessment is
an impossibility theorem or a claim that the needed mathematics does not
exist outside the inspected assets.

## Route 1: Character/constituent counting

The local `Math.CompactHomDimension.integral_character_mul_eq_finrank`
connects actual continuous finite-dimensional compact-group representations
to algebraic Hom dimensions, but supplies no explicit SU(3) torus coefficient
formula for this statistical source. Moreover, the repository's Weyl group
is SL(2,C), which is not compact; its left action and entrywise-conjugate
right action are jointly imposed. Replacing them by two independent formal
SL2/SU2 factors needs a proved invariant-space correspondence.

The pinned TauCeti assets inspected were:

- `RepresentationTheory/ClassicalGroups/WeylModule/SchurWeyl.lean`: a
  character decomposition of ordinary tensor powers under GL, not the
  required product-group statistical exterior invariant classifier.
- `WeylModule/Multiplicity.lean`: the actual Young-symmetrizer image/Hom
  correspondence, with a row-bound nontriviality criterion. It does not by
  itself evaluate the required gauge singlet in the signed mixed source.
- `WeylModule/SpecialLinear.lean`: determinant-twist restriction; its scope
  explicitly says irreducibility/exhaustiveness of SL restrictions is not
  proved there. That boundary cannot be filled by treating a character as
  an already certified constituent decomposition.

Missing: an actual invariant-dimension/constituent certificate for the signed
color/weak/Weyl exterior source, plus any compact/complexified group bridge
used in deriving it. A formal Weyl-denominator coefficient or Hilbert series
alone is not a proof of this correspondence.

## Route 2: Exact finite matrix constraints

Mathlib defines actual SL transvections and their field-level generation
machinery. TauCeti's
`Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`
supplies an SL generation theorem. Thus SL generation itself is not a
missing or assumed input of this route.

The inspected special-unitary/unitary assets do not supply the required
finite constraint theorem for the actual SU(3) action on this source. A
complete route would prove, for the actual statistical representation, that
its invariant functionals are exactly the kernel of a specified finite
matrix over an exact field. If SL shears are used for color, it must prove
the SU(3)-to-complexified-invariant correspondence; if SU(3) rotations are
used directly, it must certify their generation/exhaustiveness and exact
polynomial interpolation. Weyl constraints must keep the paired z/conj(z)
action rather than impose fictitious independent group elements.

Missing: that actual-group-to-finite-kernel equality, explicit matrix entries,
statistics transport and a proved zero/nonzero rank criterion. A finite
sample, a Lie kernel or torus neutrality is not already that equality.

## Scope decision

The scalar residual part is a bounded reusable lemma. The local invariant
classifier needs its own theorem-level construction milestone beyond the
existing finite-reduction interfaces. Under the
[workflow](../../architecture/WORKFLOW.md#endpoint-and-stop-gate), a new
theorem-level prerequisite requiring a separate milestone is a plan change,
not an automatic foundational continuation. Freeze the exact local
classifier contract before starting that milestone.

A proposed next endpoint is the finite matrix route: first certify actual
group invariance iff a finite exact kernel for these fixed input functors,
then connect its rank test to the existing finite table. Its scope must
explicitly choose the SU(3) route and the treatment of paired Weyl actions.
It must not enlarge to general group classification or silently accept an
unproved invariant correspondence. No dependencies or out-of-scope physics
are needed or authorized by this assessment.

## Subsequent authorized connection attempt

The user authorized the [matrix connection attempt](../sm-local-invariant-kernel/results.md).
Its proved generic kernel/rank criterion, finite polynomial/grid sampling,
actual Weyl generation and one-spinor control close those reusable inputs.
The actual SU(3) generating-family certificate and statistical coordinate
polynomial/source connection remain open. No full support classification
is inferred from the generic conditional kernel theorem.
