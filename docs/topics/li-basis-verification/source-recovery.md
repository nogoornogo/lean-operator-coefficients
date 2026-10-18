# Published Convention And Package Recovery

Investigation date: stage 01. This is source evidence, not a Lean certificate.

## Fixed External Source

The public author repository is
[XiaoMing-lei/ABC4EFT](https://github.com/XiaoMing-lei/ABC4EFT), inspected at
commit `848a1bec81c3459eee67055eb143108bce1f776c`.
It was retrieved into a disposable directory without adding dependencies to
this project or executing the package. The HEPForge home/download pages returned
an access-challenge page in this investigation; this does not establish that
the package is unavailable to other clients.

The pinned
[SMEFT model](https://github.com/XiaoMing-lei/ABC4EFT/blob/848a1bec81c3459eee67055eb143108bce1f776c/ABC4EFT/models/SMEFT.m)
lines 12--18 agrees with the model definition in
[Li et al., section 5](https://arxiv.org/html/2201.04639v2#S5):

| Field | Helicity input | SU(3) Dynkin labels | SU(2) | Y |
| --- | --- | --- | --- | --- |
| Q | -1/2 | (1,0) | doublet | 1/6 |
| uc | -1/2 | (0,1) | singlet | -2/3 |
| ec | -1/2 | trivial | singlet | 1 |

Conjugating the last two fields gives the right-Weyl color fundamental with
Y=2/3 and right-Weyl singlet with Y=-1. These match the gauge/chirality labels
of repository `uField` and `eField`. The repository uses integral charges 6Y:
`quark`, `upRight`, `electronRight` have charges 1, 4, -6 respectively in
[`StandardSMGaugeTensor`](../../../Physics/StandardModel/Gauge/StandardSMGaugeTensor.lean).
The spinor choices and residual actions are in
[`QqueSpinorExterior`](../../../Physics/StandardModel/Operators/QqueSpinorExterior.lean).

This label comparison does not construct a representation equivalence.
In particular, the package's number of flavors does not specify an arbitrary
residual H action. Identifying conjugate flavor carriers with `B.dual` and
`D.dual` needs an explicit pairing/identification; a dagger is not itself a
complex-linear map into an algebraic dual. Operator tensors and coefficient
tensors must also remain distinguished.

## Concrete Output Search

The first pass inspected the HTML paper and the public package's saved
examples. It missed the PDF appendices, which are absent from that HTML view. The paper's dimension-six type list includes the required
`ec† Q² uc†`, but its section-5 printed basis examples are `LLHH` and
`D⁴ H² (H†)²`. Its detailed four-fermion/six-fermion examples are different
field types. The initial conclusion that a concrete pilot could not be recovered was
premature and is superseded by the PDF finding below.

In the pinned
[SMEFT notebook](https://github.com/XiaoMing-lei/ABC4EFT/blob/848a1bec81c3459eee67055eb143108bce1f776c/ABC4EFT/tutorial/SMEFT.nb),
lines 713--719 assign `SMEFTd6 = GenerateOperatorList[SMEFT,6];` with a
semicolon. Saved cells show timing output, not the resulting operator list.
The explicit `GetBasisForType` examples at lines 846 and 1057 concern `Q³ L WL`,
not the pilot. The other tutorials and `DIM8UV.m` concern different outputs;
UV vertex data for derivative dimension-eight types do not supply the
derivative-free dimension-six contraction certificate.

The package's main code files, including `Code/Operator.m`, are encoded
Mathematica files (header `(*!1N!*)`). `wolframscript` was not found on PATH.
No decoder, replacement implementation or new runtime was installed. Static
inspection of the supplied examples has not recovered the required output;
this is not a proof that no suitable output exists.

## PDF Recovery: Equation (D.38)

The [arXiv v2 PDF, page 52, appendix D.1](https://arxiv.org/pdf/2201.04639v2#page=52)
prints the exact target in equation (D.38):

```text
field order: Q_1 Q_2 e_C†_3 u_C†_4
C^[2]_(f1 f2, f3, f4) ε^(a1 a2 a4) ε^(i1 i2) ⟨12⟩[34].
```

The PDF page was rendered and visually checked, including the epsilon index
positions and the `[2]` label. This recovers the color contraction, weak
contraction, left/right spinor brackets, slot order and symmetric Q flavor
sector from the paper itself. The neighboring (D.35) is the conjugate field
sector; it must not be substituted for (D.38).

Appendix D calls these **on-shell amplitude bases**, and explicitly distinguishes
them from the earlier operator bases, with linear transformations between them.
Thus (D.38) is a precise published candidate, not a recovered ABC4EFT runtime
p-basis array and not by itself a proved operator/coefficient equivalence.

## Resume Input And Remaining Semantic Gate

The source-recovery blocker is withdrawn. The existing plan permits using a
printed paper expression, so Mathematica output is no longer a prerequisite
for the paper-based pilot. Package execution and claims about its exact output
remain unverified.

The implemented adapter interprets this derivative-free bracket product as an
explicit local spinor contraction, accounting for the paper order `Q,Q,E,U`
versus repository `Q,Q,U,E`. The [proof dossier](../../proof/current/applications/Physics/LI_QQUE_BASIS.md) records the checked
Fermi/bracket signs, raw alternatization factor 2, finite flavor coordinates
and residual-H constraints. The epsilon/bracket basis normalizations are
explicit dictionary choices, not claims about LSZ or external-state amplitudes.

The [implementation contract](implementation-contract.md) froze these bounded
semantic obligations before coding. General on-shell-amplitude, EOM or IBP
foundations remain outside the result.

## Verification

The original source-recovery checkpoint was documentation-only: `node tools/docs/check-links.mjs` and
`git diff --check`. No Lean build or axiom audit was rerun at that checkpoint. Later proof
verification is recorded in the [topic overview](README.md); package execution
and general literature completeness remain unclaimed.
