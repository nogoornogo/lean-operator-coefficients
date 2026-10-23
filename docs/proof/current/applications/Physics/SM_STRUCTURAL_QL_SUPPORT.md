# Structural support for the fixed scalar q/l action

For the fixed ten signed three-generation Standard Model species and one
residual-neutral Higgs doublet/dual, support at every Higgs bidegree is
classified by neutral charges and a finite positive component/coupling
condition. This discharges the retained local `Allowed(T)` tests in the
original endpoint 2, for this residual-action class.

The actual theorem is `Physics.SMJointHiggsSupport.original_ql_iff` in
[SMJointHiggsSupport](../../../../../Physics/StandardModel/Operators/Support/Joint/SMJointHiggsSupport.lean).
Its hypotheses are the fixed field dictionary and a cyclic modulus k with
`[NeZero k]`, with arbitrary q,l in `ZMod k`. It has no Weyl torus reduction,
branching, source-equivalence, multiplicity/rank or other external theorem
premise. The complementary statement is `original_ql_forbidden_iff`.

For any species word p and Higgs counts h,d it proves:

```text
Allowed(SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)
  iff q/l charge(p) = 0
  and hypercharge(p) + 3(h-d) = 0
  and some m <= the proved weak slot bound is Higgs-admissible
      and satisfies the finite positive joint condition.
```

The finite condition chooses three generation occupations for each species,
then a branch of each actual single-generation exterior decomposition. It
requires a valid positive color contraction diagram and three degree-zero
SU2 Clebsch--Gordan paths, for weak, left spin and right spin. The Higgs weak
constituent participates in the weak path. Each branch preserves all these
labels jointly. No Hom, rank, Laurent coefficient or unproved matching test
remains on the right side. The
[full result dictionary](../../../../topics/sm-computable-characters/full-support-results.md)
spells out these finite choices and the construction chain.

`SMSignedCoreJointPresentation.presentation` supplies every degree of all
ten actual signed cores, including zero at overflow. The complete Q middle
splits, U/D square/cube splits and lepton exterior splits are proved source
equivalences, with conjugate actions and both spin placements retained.
`GenerationTensorSupport.allowed_iff` applies actual generation restriction
and extension in arbitrary tensor contexts by currying. The resulting
occupied core products are composed by `JointContentPresentation`.
`SMJointContentSupport.sourceEquiv` then identifies the actual ten-species
statistical source, and `restricted_iff` connects its actual semisimple
invariants to the finite test. Hypercharge necessity/neutral extension,
compact/full Lorentz coefficient comparison, scalar q/l separation and the
proved Higgs cutoff complete the original-space theorem.

This is an algebraic support classification, without computing exact
multiplicities or ranks or enumerating numerical assignment tables.
Arbitrary residual representations remain parameters of the
[general finite reduction](SM_FINITE_HIGGS_SUPPORT.md); they are not classified
here. The scope is derivative-free invariant coefficient support. UV
realization, generated interactions, derivatives/EOM/IBP, rates and numerical
phenomenology are separate questions.

The retained conditional Weyl/character extraction is an alternative
interface, not an input of this structural proof. Retired numerical
certificates remain excluded from active builds. See the
[topic](../../../../topics/sm-computable-characters/README.md) and its
[verification](../../../../topics/sm-computable-characters/full-support-verification.md).
