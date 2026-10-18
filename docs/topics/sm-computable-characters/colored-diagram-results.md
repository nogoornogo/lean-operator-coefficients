# Actual contractions as labelled diagrams

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. This continues the
[contraction plan](colored-contraction-plan.md), connecting its
[spanning](colored-contraction-results.md) and
[flag/vertex](colored-flag-vertex-results.md) results.

## Exact evaluation and positive tests

`TensorVolumeEvaluation.multiple_tprod` proves, for an arbitrary basis of
size n and arbitrary number k of determinant blocks, that the canonical
volume projection evaluates a pure tensor as the product of k determinants.
`raiseDegree_tprod` includes arbitrary remaining evaluation slots, and
`contraction_tprod` gives the complete permutation/pair/determinant formula.
No basis or content list is expanded.

The recursive degree transport now uses an actual reindexing equivalence
`TensorVolumeSplit.powerCast` instead of transporting the whole split by
an equality. Retraction laws and equivariance remain proved. This keeps
degree conversion local and exposes the pure-tensor generator formula.

`SU3ContractionDiagram` identifies the actual compact spanning contractions
with diagrams labelled by arbitrary vertex-owner maps. Each permutation at
degree q+3k supplies q evaluation pairs and k determinant triples. Its
`flag_formula` agrees with the proved polynomial chart evaluation, including
the actual defining-color volume convention. Consequently
`flag_nonzero_iff` decides nonvanishing on incident flag tensors by the
finite predicate: pair owners are distinct, and each triple-owner map is
injective.

`SU3DualContractionDiagram` proves the counterpart at degrees (q,q+3k).
The actual bidual map is retained through `dualSwap_symm_tprod`; evaluation
pairs and the volume of the actual dual basis agree with the covector flag
chart. The same positive owner predicate applies. No color self-duality,
signed character coefficient or new mathematical premise is supplied.

## Remaining local vertex and symmetry data

`TraceFreeColorVertex` adds the actual adjoint-type vertex: raw (1,1)
tensors retract equivariantly onto trace-free endomorphisms, their first
raw contraction is zero, and incident flags have exactly the expected raw
pure-tensor embedding. The existing nonzero-dimension hypothesis is explicit
and already proved for defining color. This completes the local trace and
flag construction alongside the three higher contraction kernels.

`SymmetricTensorTrace.inclusion_reindexLeft` and `inclusion_reindexRight`
prove both slot-symmetry identities on the actual normalized symmetric
images, uniformly over all degrees. They supply the symmetry input for
excluding a determinant that repeats a vertex, independently of flag tests.

## Not yet endpoint 2

The actual contraction formula and its positive flag criterion are proved
in both orientations. For necessity on arbitrary mixed sources, the
grouped vertex tensor products must still be flattened to the raw slots,
and invalid contractions must be shown to factor through a local trace
or an alternating/symmetric cancellation. The proved raw spanning theorem
then eliminates all other coefficients. Valid diagrams already have
simultaneous nonzero flag witnesses, which must be transported through
the same grouped-source maps, including dual normalization.

Finally, combine the resulting color criterion with the actual signed Q
branching, generation decompositions, joint weak/left/right spin paths,
Higgs cutoff and scalar q/l neutrality. No unevaluated Hom or surviving
coefficient test may remain in that final support predicate. Original
endpoint 2 remains open at this assembly.

See [verification](colored-diagram-verification.md).
