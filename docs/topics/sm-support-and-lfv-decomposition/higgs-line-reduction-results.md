# Eigenline Higgs Reduction: Completed Restricted Class

## What is new

The [contract](higgs-line-reduction-contract.md) is complete for complex scalar
eigenlines with inverse characters. Unlike the previous seed dressing,
the new result reduces every actual coefficient downward and reconstructs
it upward. The entire split symmetric coefficient space is equivalent to a
twisted-source invariant Hom space. No seed-existence or spanning assumption
is used. See the [proof dossier](../../proof/current/inputs/Math/HIGGS_EIGENLINE_REDUCTION.md).

For arbitrary source representation X and character chi, common Higgs/dual
pairs cancel without a finite-order assumption. For positive period k of
the whole scalar character, every degree reduces to one of k one-axis
degrees (j,0), j<k. Both all-degree prohibition and existence have exact
finite-test iff statements. The source need not be finite-dimensional or
semisimple, and the group need not be abelian.

## Public entry points

[HiggsEigenlineReduction](../../../Math/RepresentationTheory/HiggsEigenlineReduction.lean):

- lineEquiv and powerEquiv: actual symmetric-line quotient and character action.
- coefficientEquiv and coefficientEquiv_apply: the full Hom equivalence and
  explicit downward evaluation on canonical unit tensors.
- cancelPairs and primitiveReduction: remove neutral pairs at arbitrary degrees.
- finiteReduction and singleAxisReduction: reduce degrees modulo a supplied
  character period; the latter removes duplicate two-axis tests.
- all_forbidden_single_iff and exists_allowed_single_iff: exactly k tests.
- alongLines: transport other actual carriers with certified eigenline equivalences.
- scalar_source_allowed_iff: a fully discharged total-character support control.

The earlier square of k*k tests remains available as all_forbidden_iff.
Period need not be minimal; k=0 is excluded from the finite-test conclusions.

## What this does not settle

This class is not the SM weak doublet. Periodicity must hold for the scalar
representation's character under the entire acting group, not just its
residual subgroup. A Higgs coordinate or eigenvector inside a doublet is
not an equivalence of that doublet to a line.

[HiggsEigenlineBoundary](../../../Physics/StandardModel/Operators/HiggsEigenlineBoundary.lean)
certifies the distinction on the unchanged actual SM input: LL at zero Higgs
is prohibited, while LLHH is allowed whenever 2l=0. Thus residual neutrality
alone cannot reduce the weak-doublet support to zero Higgs degree. This is
not a no-go for finite reduction with additional primitive degrees.

The next missing ingredient for SM remains the actual weak-doublet
decomposition/support-exhaustiveness certificate. In addition, a consumer of
the full symmetric direct-sum scalar carrier needs its actual fixed-content
bridge to the split symmetric powers used here. This result does not pretend
to discharge either premise, increase the classified SM contents, or finish
all-content support. No VEV, mass, UV, rate or anomaly result is introduced.

## Verification and integration

All 34 new Math and three Physics public declarations are registered in the
existing strict transitive audits. [Verification](verification.md) records
focused/full builds and document checks. The working branch is unchanged;
no master merge or push is authorized.

## Subsequent SU2 foundation

[Actual SU2 tensor decomposition](su2-clebsch-gordan-results.md) now provides
the doublet/dual constituent equivalence at arbitrary degrees. It does not
extend this earlier result to all SM sources by itself: other-action
compatibility and the full-field/split joining equivalence remain open.

## Subsequent full-group and full-field connection

[Full Higgs connection](full-higgs-connection-results.md) now proves the
original fixed scalar-count/full-carrier equivalence to split symmetric powers
and retains the actual SM hypercharge factor in every weak constituent.
This closes those presentation/action obligations from the earlier checkpoint.
Classification of every fermion source's invariant Hom support, and a uniform
all-degree reduction for all contents, remain separate obligations.
