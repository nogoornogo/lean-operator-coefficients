# Kernel, Complete Null Consumer And Conjugate Weyl Sources

## Mixed EOM Kernel

For arbitrary complex linear odd/even seed maps, the actual mixed algebra
projection is onto and its kernel is precisely

\[
\ker\pi=\langle \iota_F(p(\partial)e_F(x)),
                   \iota_B(q(\partial)e_B(y))\rangle_{\mathrm{two\ sided}}.
\]

Here every polynomial derivative multiple is included. Equivalently, one may
generate by the full linear relation modules. These are proved equalities for
the existing projection, with no finiteness, homogeneity, rank or covariance
premise. The proof chooses linear splittings of generator quotients, extends
them by the free algebra functors, and proves reconstruction modulo the
generated ideal. Choice is used only inside the proof construction. IBP remains
the actual linear divergence range and is never ideal-closed.

See the [kernel source](../../../Math/Algebra/LinearJetKernel.lean) and
[mathematical dossier](../../proof/current/core/Math/LINEAR_JET_KERNEL_ADJOINT.md).

## Four-Dimensional Complete Single-Field Example

At one odd field, zero even fields and any derivative order `d + 1`, every
off-shell word is the derivative of a word of order `d`: choose a nonzero
multi-index entry and remove one copy of that direction. This proves that the
whole off-shell grade is a divergence range. The proved surjection to image
grades transports that equality through any specified linear EOM system.

For the actual free massless left-Weyl field with the existing four-dimensional
dual Lorentz direction action, the entire EOM/IBP source is therefore zero.
Its dimension is 0, its basis has empty index `Fin 0`, and every invariant
coefficient functional is zero. This determines the complete source, not just
an exhibited invariant subspace. The order-one consumer includes a specific
jet that is nonzero after EOM and has zero IBP class. Higher on-shell jets are
thus not evidence for a surviving integrated operator.

See the [general theorem](../../../Math/Algebra/LinearJetSingleField.lean) and
[actual Weyl consumer](../../../Physics/FieldTheory/Jets/WeylSingleFieldIBP.lean).
No multi-field invariant basis or nonzero interaction is claimed by this example.

## Right Equations And Hermitian Conjugation

Coefficient conjugation fixes all ordinary derivative labels, commutes with
shifts, and conjugates polynomial derivative multiplication. The right seed is
constructed by conjugating the left seed and its equation parameter. Its
explicit source relations are

\[
r^R_0=(D_0+D_3)\chi_0+(D_1-iD_2)\chi_1,\qquad
r^R_1=(D_1+iD_2)\chi_0+(D_0-D_3)\chi_1.
\]

The existing right component action is entrywise conjugation of the left
SL(2,ℂ) action. The equation parameter carries the dual left action. Actual
covariance is proved, using the reality of the existing dual four-direction
action. Conjugation sends the full left descendant module onto the right one
in both directions. The induced semilinear maps on quotient generators are
inverses, commute with shifts and intertwine the actual group actions. The
right quotient also retains the higher time-jet family before IBP.

On the exterior algebra of the paired left/right on-shell generator modules,
the chirality-swapping semilinear involution extends to an adjoint satisfying

\[
(xy)^\dagger=y^\dagger x^\dagger,\quad
(z x)^\dagger=\overline z\,x^\dagger,\quad
(x^\dagger)^\dagger=x,\quad
(D_i x)^\dagger=D_i(x^\dagger).
\]

The shifts and even derivatives commute. The adjoint commutes with the actual
paired Lorentz action, agrees with the off-shell projection, preserves the
linear divergence range, and induces an involution on the EOM/IBP vector-space
quotient. Both chiral seed families and every descendant vanish under the
actual algebra projection, which is onto. No algebra product is assigned to
the IBP quotient.

See the [conjugate equations](../../../Physics/FieldTheory/Jets/ConjugateWeylEquation.lean),
[paired adjoint](../../../Physics/FieldTheory/Jets/WeylJetAdjoint.lean) and
[physical dossier](../../proof/current/core/Physics/WEYL_CONJUGATE_IBP.md).

## Boundaries

All three frozen phases are implemented. No new dependency or external theorem
premise is introduced. The adjoint construction is on the paired odd source;
it does not assert an adjoint for arbitrary interacting even systems, a
Hilbert-space operator adjoint, a classical raised/lowered index dictionary,
a momentum/amplitude comparison, or a general EFT invariant count. Massive or
interacting equations, non-Abelian covariant derivatives and Maxwell/Bianchi
systems remain separate topics. The [source register](references.md) preserves
the literature inspection limits; [verification](verification.md) owns the checks.
