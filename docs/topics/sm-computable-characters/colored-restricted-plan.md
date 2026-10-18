# Restricted color products after resolved Q cubes

Resume `proof/sm-computable-characters` at `checkpoint 01`, targeting `master`.
The complete Q cubic and degree-nine branches are proved. Full Q degrees
four through six and general restricted-Young coupling remain open.

## Frozen next coupling statements

1. For a nonzero finite-dimensional irreducible complex representation r,
   prove every invariant scalar coefficient on trace-free End(r) vanishes.
   Use the already proved scalar/trace-free split and Schur's invariant
   coefficient line; do not assume trace-free irreducibility or self-duality.
2. For a three-dimensional r with an actual basis, construct the invariant
   trilinear coefficient `trace(x y z)` on trace-free endomorphisms. A cycle
   of three off-diagonal matrix units must give a normalized unit witness.
3. For every tensor power of that actual trace-free representation, prove
   support iff its degree differs from one, assuming r irreducible only for
   the exclusion direction. Use the scalar, pair and triple witnesses and
   tensor gluing; do not evaluate ranks or character coefficients. Apply
   to actual defining/dual SU3 color and independent joint SU2 matching.

If both orientation conventions are combined, prove an actual equivalence
between trace-free End(r) and trace-free End(r.dual) first. Use the proved
tensor/endomorphism dictionary, commutation and biduality to compare whole
endomorphism actions, then their scalar/trace-free splits and finite scalar
summand cancellation. Do not assume adjoint self-duality. This permits an
arbitrary binary word of the two actual orientations to reduce to its total
number of trace-free leaves before applying the power criterion.

These close a restricted subclass, not arbitrary mixtures with symmetric
or higher Young components. No new external premise, dependency change,
numerical certificate or raised Lean limit is permitted. Use the existing
guarded focused/audit/full-build acceptance checks and coherent commits.

## Frozen next Q obligation, still unproved

For a pulled-back doublet W and arbitrary finite-dimensional A, the next
quartic source target is an actual equivariant split

```text
Lambda^4(A tensor W)
  = (Lambda^4 A tensor Sym^4 W)
      + (K211(A) tensor Sym^2 W) + K22(A),
K211(A) = ker(A tensor Lambda^3 A -> Lambda^4 A),
K22(A)  = ker(Sym^2(Lambda^2 A) -> Lambda^4 A).
```

The kernel maps must be constructed from exterior multiplication, including
the symmetric descent in the second line. Actual embeddings and complete
inverse/exhaustion relations, followed by retained color/weak resolution,
are needed. This displayed target is a proof obligation, not a supplied
branching premise. The cubic cancellation bridge only becomes applicable
once an actual quartic source comparison is proved. Degree five/six need
further such identities. No numerical or character-shadow fallback is an
accepted substitute.

## Verified coupling outcome

The subsequent [quartic checkpoint](colored-quartic-results.md) constructs
both kernel maps and their complete auxiliary splits, isolates the actual
top column, and proves the symbolic dimension identity. The displayed
three-component quartic equivalence has since been proved by the
[two-component continuation](colored-quartic-two-results.md). The retained
color/weak resolution required for full Q classification remains open.

The singleton coefficient exclusion, normalized triple witness, all-degree
trace-free power criterion, actual dual-endomorphism identification and
arbitrary two-orientation tensor-word iff are proved; see
[results](colored-restricted-results.md) and
[verification](colored-restricted-verification.md). This is a complete
restricted subclass. The displayed quartic source target and arbitrary
mixtures with symmetric/higher Young color components remain obligations.
