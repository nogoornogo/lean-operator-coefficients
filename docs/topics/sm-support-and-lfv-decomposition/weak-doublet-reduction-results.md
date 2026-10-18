# Weak-Doublet Reduction: Weak-Singlet Source Class Completed

## Result

The [contract](weak-doublet-reduction-contract.md) is complete. Unlike the
earlier eigenline result, the Higgs here is the actual two-dimensional SM
weak representation, with arbitrary symmetric powers and its algebraic dual.
For a whole weak-singlet source X,

    C(h,d)=Hom_G(X tensor (Sym^h H tensor Sym^d H-dual), C),
    h!=d implies every coefficient is zero,
    C(r,r) equivalent to Hom_G(X,C) equivalent to C(0,0).

Allowance and prohibition have exact iff statements. Every coefficient at
balanced degree is reconstructed from a unique zero-Higgs source coefficient.
There is no conditional seed-existence, finite spanning or character-period
premise. See the [proof dossier](../../proof/current/inputs/Math/WEAK_SINGLET_HIGGS_REDUCTION.md).

## Construction and entry points

- [SymmetricDualPairing](../../../Math/RepresentationTheory/SymmetricDualPairing.lean)
  constructs actual symmetric quotient pairing and covariance. The diagonal
  formula is (phi(v))^r, including r=0.
- [WeakDoubletScalars](../../../Math/RepresentationTheory/WeakDoubletScalars.lean)
  reuses actual all-degree SU2 irreducibility, proves duality, unbalanced_zero,
  unique and balancedEquiv. The symmetric scalar coefficients are exhaustively
  classified; a neutral raw tensor is not used as a spanning premise.
- [WeakSingletHiggsReduction](../../../Math/RepresentationTheory/WeakSingletHiggsReduction.lean)
  proves slice, factor, evaluate, assemble, both inverse identities, equiv,
  zeroDegreeReduction and the all-degree prohibition iff.
- [WeakSingletHiggsSupport](../../../Physics/StandardModel/Operators/WeakSingletHiggsSupport.lean)
  proves the actual SM weak inclusion and Higgs action correspondence, plus
  a scalar coefficient equivalence. Its matter consumer certifies the weak
  action of uR,dR,eR and signed dual fields and all their exterior degrees.
  matterEquiv, matterZeroDegreeReduction, matter_allowed_iff and
  all_matter_forbidden_zero_iff have no unproved weak-triviality premise.

The Math endpoint still exposes the chosen representation-class hypotheses
as actual action identities. The Physics matter consumer discharges them;
color, Weyl, hypercharge, flavor and fermion alternation are retained.
This removes the infinite Higgs-degree problem for that field alphabet, but
does not compute its zero-Higgs fermion coefficient spaces automatically.

## Boundaries and next work

The whole source must have trivial weak action. Merely possessing a singlet
component does not qualify the rest of the source. The LL/LLHH counterexample
to unrestricted zero-degree reduction remains valid; it lies outside this
source class. Q/L doublet sources need further weak constituents and primitive
Higgs degrees. The general Clebsch-Gordan/source decomposition connection
and full fixed-input support classification remain open.

All statements use split symmetric Higgs/dual powers. A selected subspace of
Sym^(h+d)(H direct-sum H-dual), or the original full mixed species carrier,
must be connected by a proved content bridge before transferring these iff
statements there. This endpoint does not silently identify those presentations.
Multiple Higgs copies and VEV/mass/UV/quantum/rate questions are not added.

## Verification and branch

The new sources have 47 Math and 18 Physics public declarations; every one is
registered in strict transitive audits. [Verification](verification.md) records
focused/full checks. The existing branch is reused from checkpoint 01. No master
merge or remote push is authorized.

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
