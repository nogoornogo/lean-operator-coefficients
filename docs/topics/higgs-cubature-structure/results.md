# First-Collinear Structural Moment Identity

The [three-family result](remaining-results.md) extends this completed pilot
without changing its formula or assumptions.

The first collinear family has a structural proof of its complete fourth moment
in [CollinearMoments.lean](../../../Math/Algebra/HiggsFourWaveCubature/Structural/CollinearMoments.lean).
For every ordered wave index `s,t,u,v` and direction index `i,j,k,l`,
`Structural.collinear_moments` proves the original `sumMoment 1 = expected 1`.
The unchanged 140 `moments1_*` theorems now forward to that result.
Final resource comparison and acceptance checks are recorded in
[verification](verification.md).

## Proof

Multiplying the three spatial coordinates by the Gaussian integer `i` converts
the Minkowski pairing into a Euclidean pairing. Existing coordinate-sign
cancellation eliminates components without paired direction indices. Six
coordinate swaps identify all remaining components with the diagonal component
`A` and three paired components `B,C,D`. One Hadamard diagonal constraint gives
`A = B+C+D`. The abstract
[tensor shape lemma](../../../Math/Algebra/HiggsFourWaveCubature/Structural/TensorShape.lean)
therefore expresses the tensor as three products of Kronecker deltas.

The [node certificates](../../../Math/Algebra/HiggsFourWaveCubature/Structural/CollinearChecks.lean)
prove these swaps and the Hadamard constraint by reindexing the unchanged 72
nodes. A common fourth root of unity may change a node's quadratic Gram matrix
by a sign. The sign has square one, so products of Gram entries are constant.
Contracting the tensor in its three pairings gives

$$
\begin{pmatrix}16&4&4\\4&16&4\\4&4&16\end{pmatrix}
\begin{pmatrix}B\\C\\D\end{pmatrix}
=72\begin{pmatrix}G_{st}G_{uv}\\G_{su}G_{tv}\\G_{sv}G_{tu}\end{pmatrix}.
$$

Exact linear combinations determine, for example,
`B = 5 G_st G_uv - G_su G_tv - G_sv G_tu`; the other two coefficients follow
from the other rows. Cancellation in Gaussian integers suffices: no division
or numerical inversion is used. Undoing the spatial phases gives exactly the
original Minkowski formula, including its normalization.

## Computational Boundary And Compatibility

Finite kernel reduction remains for node transports, their involutions,
phase/Gram identities and small direction-index combinatorics. The 35 complete
fixed-wave moment calculations are no longer proof premises. No finite-group
order, generation statement, Python result or literature classification is a
Lean premise. Python only reproduces exact candidate data that Lean checks.

`raw`, `count`, `gram`, `factor`, `expected` and every old theorem statement
are unchanged. The transverse and second-collinear moment proofs are unchanged.
The Higgs coefficient theorem retains its original hypotheses and physical
scope. This pilot establishes the route for one family and makes no claim that
the other families admit the same transports or normalization argument.
