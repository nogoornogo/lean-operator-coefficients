# Residual Separation And Finite-Rank Completion

## Proved part

For any positive cyclic order k, q,l in ZMod k, signed species pattern p,
weak degree m and hypercharge twist delta, `QLFiniteSupport.test_allowed_iff`
proves the exact statement

    Allowed(T(q,l,p,m,delta)) iff
      charge(q,l,p)=0 and Allowed(LocalTest(q,l,p,m,delta)).

Here charge is the sum of the existing actual signed charges
[q,q,q,l,l,-q,-q,-q,-l,-l]. `LocalTest` restricts the actual statistical
source/constituent representation to GaugeGroup x WeylSpinor.Group. It keeps
the original carrier, source image, exterior relations, weak constituent and
hypercharge twist; it is not an ordered-tensor or torus-only replacement.

The generic `ScalarResidualSupport.equiv` preserves the actual linear
coefficient in both directions when the residual character is neutral.
The actual source scalar action is proved by transport from the typed slot
tensor to its exterior-statistical image, including images that vanish.
Higgs constituents are residual neutral. No seed positivity is assumed.

`QLFiniteSupport.original_allowed_iff` composes this with the preceding
original-carrier finite Higgs reduction:

    Allowed(OriginalSpace(q,l,p,h,d)) iff
      charge(q,l,p)=0 and
      exists m : Fin(N_p+1), Admissible(h,d,m) and
        Allowed(LocalTest(q,l,p,m,h-d)).

`field_local` proves the actual species actions on local group elements
(g,1) agree with those at q=l=0. This checkpoint does not claim a newly
constructed whole-source coefficient equivalence across different q/l or
cyclic orders. The displayed LocalTest still uses the actual supplied
q/l source carrier and retains its group/field dictionary.

The signed-charge controls for DUQL/QQUE/QQQL/DUUE are 3q+l; the six-quark
control is 6q and the LL control is 2l. Those agree with the previously
proved individual family classifications. Their local witnesses and full
support results are not newly reproved by this checkpoint.

## Subsequent endpoint completion

The [compact-kernel completion](../sm-compact-kernel-completion/results.md)
constructs the missing actual-group classifier. Six color, two weak, one
hypercharge and `4(n+1)` Weyl tests are proved exhaustive on every retained
statistical source/Higgs constituent. `SMQLFullKernel.original_allowed_iff`
therefore replaces `Allowed(LocalTest)` by the rank of its explicit finite
constraint matrix for every content and constituent.

This completes the requested predicate-level q/l support classification. It
does not enumerate the ranks, recount the 572 assignments or classify new
residual actions. No Lie/group or compact/complexified correspondence is used
as an unchecked premise.
