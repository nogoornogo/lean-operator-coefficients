# Structural Moments For All Three Higgs Families

The transverse and second-collinear ordered moment identities have structural
Lean proofs. They join the completed first-collinear proof. The old 420 entry
statements remain unchanged; final consumer and resource checks are recorded in
[remaining verification](remaining-verification.md).

| Family | Nodes | Structural route |
| --- | ---: | --- |
| Transverse (`r=0`) | 288 | Coordinate swaps and a Hadamard constraint give tensor shape; Gram contractions fix its factor four |
| First collinear (`r=1`) | 72 | The same tensor shape and Gram contractions give unit normalization |
| Second collinear (`r=2`) | 72 | Exchange wave labels 2 and 3 and involutively reindex the first-collinear nodes |

The transverse proof reuses the common
[tensor-shape theorem](../../../Math/Algebra/HiggsFourWaveCubature/Structural/TensorShape.lean).
Exact [node certificates](../../../Math/Algebra/HiggsFourWaveCubature/Structural/TransverseChecks.lean)
supply coordinate swaps, the Hadamard constraint and phase-covariant Gram values.
The common Gram sign has square one. Three contractions give the same matrix
with diagonal 16 and off-diagonal 4, with right-hand side 288 times the three
Gram products. Solving by exact linear combinations gives the same polynomial in this
family's Gram entries, multiplied by four. Each family uses its own unchanged Gram matrix. The
[ordered theorem](../../../Math/Algebra/HiggsFourWaveCubature/Structural/TransverseMoments.lean)
undoes the spatial phases to recover exactly `expected 0`.

The [second-collinear transport](../../../Math/Algebra/HiggsFourWaveCubature/Structural/SecondCollinear.lean)
proves the raw coordinate identity and a node bijection. Transporting the sum and
Gram matrix gives exactly `expected 2`. Its proof uses the first-collinear
structural theorem directly, without the 35 old fixed-wave certificates.

All three families retain finite kernel checks for small node/phase/Gram and
index identities. Those checks supply structural hypotheses internally; no
Python output, finite-group generation/order or paper-completeness premise is
accepted. The final public statements add no caller hypothesis.

All raw nodes, conservation/null identities, counts, Gram matrices, scale
factors and formula definitions are unchanged. This closes the remaining-family
proof refactor, without extending the Higgs theorem's physical interpretation,
allowed interactions or input interface.
