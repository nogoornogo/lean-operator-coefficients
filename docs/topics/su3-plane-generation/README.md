# Actual SU(3) Plane Generation

- Status: completed
- Result type: proved actual SU(3) algebraic generation
- Working branch: `proof/su3-plane-generation`
- Integration target: `proof/sm-local-invariant-kernel`
- Parent exception: bounded child of the unmerged matrix-connection topic.
- Authorization: user requested planning and formalization through the stop
  condition at stage 01. No master integration or push is authorized.

Master integration was authorized at stage 02 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

## Frozen plan

Prove algebraic generation of the actual `Matrix.specialUnitaryGroup (Fin 3) ℂ`
by two-coordinate determinant-one unitary matrices. Define the family as
actual matrices fixing one coordinate basis vector; construct explicit
normalized complex two-coordinate rotations within this family.

1. Prove membership and coordinate action for embedded SU(2)-form matrices.
2. Prove a two-coordinate elimination lemma, including the zero-pair case,
   using exact real square-root normalization.
3. Eliminate two coordinates of the first column of an arbitrary actual SU(3)
   matrix. Use unitarity to obtain a first row/column equal to the first
   coordinate vector, leaving a two-coordinate determinant-one unitary block.
4. Prove closure of the plane family is top and consume the existing
   generator-invariant theorem for arbitrary representations of actual SU(3).

No statistical-source polynomial descent, finite parameter sampling, Lie
algebra correspondence, general SU(n) classification, dependencies or pin
changes are included. No irreducibility-to-generation implication is used.
Helpers for the explicit three-dimensional matrix decomposition are in scope.
Stop if the construction requires a new general spectral/topological theorem
or a change to the actual group, trust boundary or dependencies. Ordinary
matrix/complex arithmetic obstacles are implementation work, not stop gates.

## Acceptance

Focused Lean builds; persistent strict transitive axiom audit; serialized full
`lake build`; layout, local links and diff checks; reviewed verified commit.
A partial result must identify the unproved generation obligation precisely.
See [results](results.md) and [verification](verification.md).

## Sources

- [Parent result](../sm-local-invariant-kernel/results.md)
- [Small special unitary actions](../../../Math/RepresentationTheory/Unitary/SmallSpecialUnitary.lean)
- [Generator invariant tests](../../../Math/RepresentationTheory/GeneratorInvariantTests.lean)

## Authorized stages 2 and 3

The [statistical-kernel child](../sm-statistical-finite-kernel/README.md) extends
the plan beyond this completed generation endpoint. It proves finite actual
Weyl tests through content statistics and the exact partial local coefficient
connection; compact SU(2) finite sampling remains a separate stop gate.
