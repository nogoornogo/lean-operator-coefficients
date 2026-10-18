# Actual 40: Selected SM Multiplicities

The requested endpoint is proved for `ExoticWedgeKernel.representation`, the
actual dual wedge kernel, restricted along the standard SM embedding:

| Species, with integral charge 6Y | Proved full-SM Hom multiplicity |
| --- | --- |
| Q, charge 1 | Positive |
| uc, charge -4 | Positive |
| ec, charge 6 | Zero |

The combined theorem is `FortyElectronExclusion.selected_multiplicity_result`.
The previous `forty_eq_actual_restriction` identifies its carrier with the
actual restriction. No supplied branching table, character profile, mass
matrix, VEV or literature premise is used.

## Equivariant projection onto the actual kernel

[WedgeKernelProjection](../../../GUT/SU5/Representations/WedgeKernelProjection.lean)
constructs a section of Five tensor Ten -> third exterior power. On a pure
triple its value is the cyclic sum of x tensor (y wedge z), divided by three.
Alternatization and the exterior universal property prove equivariance and
that wedge composed with the section is the identity. Identity minus section
composed with wedge is therefore an actual equivariant kernel projection.
No semisimple splitting hypothesis is introduced.

## Positive Q and uc

[FortySelectedCopies](../../../GUT/SU5/Branching/FortySelectedCopies.lean)
uses the existing full-SM Five and Ten equivalences. It embeds and probes
Weak tensor upRight-dual and Color tensor electronRight-dual. On pure wedges
each probe after kernel projection equals 2/3 times the original block tensor,
and both probes are nonzero.

Charge-preserving equivariant equivalences identify these blocks with Q-dual
and upRight. Restricting the probes to the actual kernel and dualizing gives
explicit nonzero maps Q -> forty and uc -> forty. Their full-SM Hom spaces
have positive finite dimension. Weak epsilon duality is included; hypercharge
is retained. This proves more than existence of vectors at the relevant charges.

## No electron singlet at charge 6

[FortyElectronExclusion](../../../GUT/SU5/Branching/FortyElectronExclusion.lean)
proves every equivariant map from the original kernel to electronRight is zero.
Hypercharge excludes all mixed color/weak triples at charge -6. On three color
inputs, the actual SU(3) action and `SMEpsilonUniqueness.color_unique` force
the functional to be a scalar multiple of epsilon-three. Basis extensionality
extends this to the whole ambient representation. The functional factors
through the third exterior power and vanishes on the wedge kernel.

The equivariant kernel projection extends any kernel functional to the ambient
representation. Biduality then proves every map ec -> forty vanishes and its
Hom space has dimension zero. Charge 6 itself is not excluded wholesale;
the result excludes the color and weak singlet with that charge. It does not
identify the entire charge-6 block with an octet.

## Remaining boundary

The requested positive/zero result is complete. Exact equalities Q=1 and uc=1,
the full decomposition of other SM components, and an arbitrary-mass
presentation for variable copies of 40 and conjugate 40 remain separate work.
This alone does not establish the extended-family copy-count obstruction or
exclude conjugate mass partners.

The subsequent [mass continuation](exotic-mass-results.md) now treats both
conjugate orientations in an exotic-only copy family, without fixing a mass.
It proves survival bounds and an SM-compatibility exclusion. The larger family
including 10 and bar5 and the full spectator decomposition remain open.

The subsequent [full-family result](full-family-results.md) closes the
arbitrary-mass index and coefficient connection for 10/bar5/40/50 and conjugates
in the fixed gauge-only, exact-SM class. It derives enough actual hypercharge
rows to avoid the still-unproved full spectator decomposition.

The [previous result](forty-extraction-results.md) still supplies opposite-
species absence and same-orientation pairing exclusions. See
[verification](verification.md) for the strict audit and build record.
