# Actual color products needed by Q middle degrees

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. This proves the next bounded
color identities in the [completion plan](colored-support-completion-plan.md).

## Constructed kernels

Write C for the actual defining SU3 representation, E for its trace-free
endomorphisms, and H21 for the previously constructed symmetric-square/dual
contraction kernel. The new actual subrepresentations are

```text
H31 = ker (Sym^3 C tensor C* -> Sym^2 C)
H22 = ker (Sym^2 C tensor Sym^2 C* -> C tensor C*).
```

The first contraction sums the three covector evaluations. Its right inverse
inserts the canonical coevaluation tensor and divides by `dim(C)+2`.

The second contraction is the four-term partial trace. If I denotes its
coevaluation insertion and P is a vector/dual tensor, the universal identity is

```text
partialTrace(I(P)) = (dim(C)+2) P + trace(P) coevaluation.
```

An explicit scalar/trace correction inverts this operator. Both constructions
work in any finite dimension and for any group action; the denominators are
proved nonzero symbolically. Their actual kernel complements and full
equivariant source equivalences are proved, without a numerical dimension,
rank, character coefficient or irreducibility premise.

Nonzero kernel vectors are constructed from a nonzero vector a and covector f
with f(a)=0, and distinguished by scalar polynomial evaluations. This proves
nontriviality of H31, its dual-species analogue, and H22 for the actual C.
Nontriviality is not asserted to prove irreducibility or a general coupling rule.

## Complete source identities

`SU3MiddleColor.adjointSquare` proves

```text
E tensor Sym^2 C = H31 + H21(C*) + Sym^2 C + C*.
```

`squareDualSquare` proves

```text
Sym^2 C tensor Sym^2 C* = scalar + E + H22.
```

`adjointPair` proves

```text
E tensor E = scalar + E + E + Sym^3 C + Sym^3 C* + H22.
```

Every equality is an actual full-group representation equivalence. The
adjoint products follow by regrouping tensor sources, applying the proved
exterior/symmetric and contraction splittings, and cancelling common finite
summands by the existing finite-length theorem. The trace-free representation
on C* is compared to E by an existing proved equivalence.

These five modules add 61 strict transitive declarations. They do not finish
Q five/six branching: the remaining step is to compose their retained weak
actions with the [actual exterior-weight source comparison](exterior-weight-slice-results.md)
and isolate the spin multiplicities. The positive general restricted-color
coupling rule and the full original q/l support endpoint remain open.

See [verification](colored-middle-products-verification.md).
