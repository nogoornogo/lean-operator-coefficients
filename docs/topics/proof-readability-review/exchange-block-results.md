# Structural exchange and product blocks

This is an earlier partial checkpoint. The completed Li source/orbit
replacement is recorded in [the current result](source-replacement-results.md)
and [its verification](source-replacement-verification.md).

## What changed

The resumed route avoids the monolithic finite-data file. It replaces the
unexplained `extra` array and its 25-entry-by-four-generator invariance check
with a pairing between two explicit two-dimensional blocks:

$$
A=-C_0+2C_1-C_3,\quad B=C_0+2C_2-C_4,
\qquad X=S_0-S_1+S_2-S_3,\quad Y=S_0+2S_1+S_2+2S_3,
\qquad e=A\otimes X+B\otimes Y.
$$

The generator actions on `(A,B)` and `(X,Y)` are now displayed separately.
Up exchange acts as `(I,-I)`. The middle down exchange swaps both pairs.
Each remaining down exchange acts by dual reflections:

$$
(A,B)\mapsto(-A,-A+B),\qquad (X,Y)\mapsto(-X-Y,Y).
$$

The two cross terms cancel symbolically in the pairing. The implementation
proves tensor transport once for arbitrary vectors, then applies these block
actions. Small five-coordinate checks identify these four named vectors under
the existing actions; they remain explicit scalar arithmetic. No rank,
25-by-25 inverse or large closed Boolean certificate is used by this proof.
The numeric entries are not merely moved into another dense table.

## A complete four-dimensional reconstruction

In `LiSixQuarkPairBlock`, write a local array in this product as
`a AX + b AY + c BX + d BY`. Four scalar evaluations determine these
coefficients. Define

$$
E=AX+BY,\quad R=AX+2AY-2BX-BY,
$$
$$
U=(-AX+AY+2BX+BY)/3,\quad V=(AX+2AY+BX-BY)/3.
$$

The proved symbolic reconstruction, valid for arbitrary complex coefficients, is

$$
aAX+bAY+cBX+dBY=
\frac{a+d}{2}E+
\frac{2b-a+d-2c}{6}R+
(b-a+d)U+(a-d+c)V.
$$

The normalized probe reads `(a+d)/2`. Hence the probe kernel in this product
is reconstructed from the three displayed generators `R,U,V`. This is a
proved small spanning result, not a numerical rank assertion. Identification
of all these generators with specified printed Young orbits is a separate
remaining dictionary obligation; no such identification is assumed here.

## Whole-array reduction

`LiSixQuarkBlockCoordinates` gives explicit extraction and reconstruction
formulas for a color `2+3` decomposition and a spin `2+3` decomposition.
Each inverse identity is checked symbolically on five arbitrary coordinates.
Tensor distribution composes these into the actual linear equivalence

$$
V_{\rm local}\simeq
(V_2\otimes V_2)\times(V_2\otimes V_3)\times
(V_3\otimes V_2)\times(V_3\otimes V_3).
$$

Thus the large local problem has blocks of sizes 4, 6, 6 and 9. This is a
linear coordinate equivalence; it is not by itself a complete equivariant
identification of every component with a printed seed orbit.

Separately, `LiSixQuarkExchangeBlocks` derives up-exchange involutivity from
swapping the actual slots twice, using invariant reconstruction injectivity.
It proves the unique even/odd splitting and a corresponding kernel-spanning
criterion, with no array-entry enumeration for involutivity.

## Remaining scope

This continuation has genuinely replaced the extra-component table and its
invariance proof, and proved independent product-block reconstruction.
It has **not** removed `LiSixQuarkFiniteData` or the original selected-orbit
matrix certificate. The 6-, 6- and 9-dimensional block reconstruction by printed
orbits, and the dictionary for the new small generators, remain to be proved.
The old basis and flavor statements retain their original proof dependencies.

A lightweight exploratory projection of the selected columns suggests that
these coordinate blocks separate the old problem substantially. That external
calculation is not a theorem premise or a certified spanning result. The next
bounded target should be a semantic printed-orbit bridge in one product block,
not another full evaluation of the monolithic finite-data file.
