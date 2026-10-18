# Closed coupling of arbitrary trace-free color words

The [bounded plan](colored-restricted-plan.md) proves a complete necessary
and sufficient rule for arbitrary binary tensor words of actual trace-free
End(color) and trace-free End(dual color). It also retains independent joint
SU2 matching. This extends the [exterior-word rule](colored-middle-results.md)
to another restricted class. General mixtures with symmetric/higher Young
components and Q core degrees four through six are still open.

## The closed rule

`SU3TraceFreeWord.Word` has scalar, direct trace-free, conjugate trace-free,
and binary tensor constructors. Any ordering and parenthesization are
allowed, and there is no bound on the number of factors in this theorem.
`allowed_iff` proves

```text
Allowed(Invariants(actual color word)) iff number of trace-free leaves != 1.
```

The empty word has a scalar coefficient; one leaf is forbidden; every
word with at least two leaves has an actual nonzero coefficient.
`forbidden_iff` proves the corresponding exact exclusion. These are tensor
words of the specified actual kernels. An additional symmetric/exterior
quotient of the entire word is not covered automatically.

`joint_iff` additionally requires simultaneous equality of both independent
SU2 symmetric-power labels. The complete color word is assembled before
separating the independent color/weak/spin group actions.

## Proof of the exclusion

`TraceFreeCoefficientExclusion` treats any nonzero finite-dimensional
irreducible complex representation r. It identifies the entire invariant
coefficient space of End(r) with the scalar line via tensor-Hom curry,
biduality and the proved Schur lemma. An invariant coefficient on its
trace-free kernel extends to End(r) through the actual trace-free projector.
It must be proportional to normalized trace, but vanishes on the scalar
identity. Therefore that proportionality scalar and the original coefficient
both vanish. The proof assumes neither irreducibility of the trace-free
representation nor a trace-form self-duality theorem.

The actual SU3 defining representation and its dual already have proved
irreducibility. Their standard bases discharge all finite-dimension/nonzero
conditions. No new irreducibility premise is supplied by this continuation.

## Positive witnesses in every degree

`TraceFreeTrilinear.coefficient` is the conjugation-invariant trilinear
coefficient `trace(x y z)`. A cycle of off-diagonal rank-one maps in an
actual three-vector basis evaluates to one. The earlier bilinear trace
coefficient supplies the two-factor unit witness.

`SU3TraceFreePowers.positive` proves every tensor degree other than one by
scalar/pair/triple witnesses and induction adding pairs. Its `allowed_iff`
combines this with the singleton exclusion. It does not compute an invariant
dimension, a character coefficient or a rank numeral. The generic positive
construction only requires the actual basis; irreducibility is needed for
the exclusion and is discharged for the actual color cases.

## Both orientations, with a proved equivalence

`TraceFreeDualEnd.equivalence` compares End(r) and End(r.dual) via actual
tensor/endomorphism dictionaries, commutation and biduality. Their proved
scalar/trace-free decompositions give an equivalence with a common scalar
summand. The proved finite-length cancellation bridge removes that scalar,
giving an actual equivalence of the two trace-free representations. This
works without an irreducibility premise.

`SU3TraceFreeWord.orientations` specializes it to actual color. The recursive
word equivalence then identifies every orientation/ordering with a power
of the defining-color trace-free action. No unproved matching test or
assumed adjoint identification remains in the word criterion.

No numerical rank/multiplicity certificate, Weyl input, new literature
premise, custom axiom, dependency change or raised proof limit is used.
The original full mixed q/l support classification is still incomplete.
See [verification](colored-restricted-verification.md).
