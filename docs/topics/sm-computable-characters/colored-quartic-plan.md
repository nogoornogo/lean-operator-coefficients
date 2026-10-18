# Quartic exterior source: algebraic construction

Current result: the generic three-component doublet equivalence and the
previously unresolved top-column kernel identification are proved; see
[two-component results](colored-quartic-two-results.md) and
[verification](colored-quartic-two-verification.md). The full Q color/weak
resolution has since been proved in the
[color/weak continuation](colored-quartic-resolution-results.md). Degrees
five/six and the general mixed support classification remain open.

Resume `proof/sm-computable-characters` at `checkpoint 01`; integration target
`master`, with no merge or push authorized. This implements the frozen
[quartic obligation](colored-restricted-plan.md#frozen-next-q-obligation-still-unproved).

## Statements and interfaces

For any complex vector space A, construct exterior multiplication maps
`m13 : A tensor Lambda^3 A -> Lambda^4 A` and
`m22 : Sym^2(Lambda^2 A) -> Lambda^4 A`. Prove the latter descends through
the symmetric quotient, rather than supplying this as an assumption.
Define the kernels K211 and K22 using these actual maps.

Construct natural sections by alternatizing the universal four-variable
maps `a tensor (b wedge c wedge d)` and
`sym((a wedge b) tensor (c wedge d))`. Composition with multiplication is
`4!` times the identity. Normalize once to obtain kernel projections and
complete source/kernel splits, with inverse identities. Retain arbitrary
group actions in equivariant versions. No basis, representation rank,
character coefficient, or finite table is to be evaluated.

Next compare these sources with `Lambda^4(A tensor W)` for an actual
pulled-back SU2 doublet. The endpoint remains an actual equivalence with
`(Lambda^4 A tensor Sym^4 W) + (K211 tensor Sym^2 W) + K22`, including
exhaustion, followed by the retained color/weak resolution for Q. A split
of the auxiliary sources alone does not establish this endpoint.

## Acceptance and stopping boundary

Use existing exterior/symmetric descent, naturality and proved finite
summand cancellation. Keep dependency pins, default Lean limits and external
premises unchanged. Numerical rank/character certificates are excluded.
Run guarded focused checks, extend strict transitive axiom audits, run
aggregate and full builds, layout/link/retired-certificate and diff checks,
and commit verified coherent milestones. Continue within these interfaces;
record an exact unresolved theorem and stop before introducing a different
foundational theory or an unapproved branching premise.

## Checkpoint at checkpoint 02 and its remaining maps

The two actual multiplication kernels, normalized natural sections,
equivariant auxiliary splits, symbolic three-branch dimension balance,
and the split top-column embedding are proved; see
[results](colored-quartic-results.md) and
[verification](colored-quartic-verification.md).

The endpoint is not complete. For a doublet W, construct actual maps from
`K211(A) tensor Sym^2 W` and `K22(A)` into the kernel of the proved
top-column retraction, and prove the combined map injective. The proved
`candidate_dimensions` / `surjective_of_injective` then supply exhaustion.
The retained color/weak resolution is still a subsequent obligation.
Do not replace those maps or independence by equal dimensions, a character
shadow or an additional branching hypothesis.

## Two-component continuation

Resume at `checkpoint 02` on the same branch. Construct insertion and contraction
maps from the actual doublet determinant tensor/form, using the associated
fourth tensor power. Establish their universal composition identities on
decomposable exterior/symmetric tensors before restricting to K211 and K22.
Small, fixed four-slot permutation identities are symbolic algebra here;
they are not evaluations of representation ranks or character coefficients.
Prove the cross compositions vanish and use the already proved symbolic
dimension identity for exhaustion. Retain both arbitrary A actions and the
actual doublet action, then pull back along the specified group map. Keep
the earlier trust, resource, verification and scope boundaries unchanged.

The two insertions and their left inverses, vanishing cross contractions,
three-way independence, symbolic exhaustion and full-action equivalences
have now been proved. Projecting the insertions into the previous
top-column kernel and restricting the inverse contractions proves its
actual two-component equivalence as well. The next open task is the
retained color/weak resolution, not another unspecified quartic branching
premise. No completion of the original full q/l support endpoint is claimed.
