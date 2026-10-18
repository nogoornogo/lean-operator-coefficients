# Georgi-Glashow Fermion-Sector Exterior Benchmark

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

External reference roles and the stage 01 bibliographic checks are recorded
in the [individual reference review](../../../REFERENCE_REVIEW.md).

## 1. Result and status

The retained actual SU(5) representation `n(10 + bar5)`, with `n > 0`,
now supplies the positive-constituent hypotheses and the actual nonzero
qque alternating/exterior coefficient. This is a pre-electroweak fermion-sector
application, not a full interacting or phenomenologically viable model.

## 2. Inputs and conclusion

### Inputs And Derived Data

The source is the existing Hilbert space and SU(5) action in
[MatterSource](../../../../../GUT/SU5/SelectionRules/MatterSource.lean).
The user supplies only a compact topological group H, a continuous homomorphism
`R : OrdinaryAction H n` into the unitary centralizer of that action, and `n > 0`.
H need not be Abelian, finite, or faithfully represented. This example retains
unitarity of R; it does not claim to construct the most general nonunitary
commuting action.

[GeorgiGlashowSource](../../../../../GUT/SU5/SelectionRules/GeorgiGlashowSource.lean)
constructs the product SU(5) x H action and **zero** symmetric mass. Hence the
mass radical is the original matter, with an actual equivariant linear
equivalence, not merely the same dimension or character. Restriction along
the standard SM-cover homomorphism gives the continuous compatible action.

The existing unitary branching equivalences for 10 and bar5 yield an actual
SM-equivariant equivalence with n copies of Q, up-left, down-left, lepton and
electron-left, and zero singlets. This equivalence forgets H; it does not
assume a common flavor action or prescribe its irreducible constituents.
The two actual conjugations are supplied by SU(5), and T-unitarity follows
from the existing gauge action.

### Positive Support And Exterior Endpoint

The reusable [ExactSMAutomaticPositive](../../../../../Physics/StandardModel/Spectrum/ExactSMAutomaticPositive.lean)
lemma combines an exact SM spectrum with the structural conjugation hypotheses:

1. Opposite-species multiplicities vanish, so species indices are actual target characters.
2. The same spectrum derives the four-weight target equations.
3. The two conjugations give equality of the Q/up/e target characters.
4. Positive Q dimension and character uniqueness give a common positive
   coefficient in the automatically constructed normalized presentation.

Thus the pairwise Q/up and Q/e support condition follows as well. It is an
output, not an additional model hypothesis. No explicit decomposition of the
H representation or coefficient table is supplied by the user.

[GeorgiGlashowQque](../../../../../GUT/SU5/SelectionRules/GeorgiGlashowQque.lean)
passes this derived condition to `AutomaticSpeciesQque`. It constructs actual
participating Q subspaces in the radical K and right-handed up/electron
subspaces in K.dual, with their spinors. The qque-originating alternating
coefficient and its descent to `ExteriorPower 4` are nonzero and invariant
under `(SM-cover x H) x SL(2,C)`.

Closed one-generation and three-generation controls use the trivial group
PUnit and trivial residual action. `species_counts` proves that the three
actual SM multiplicities are `(n,n,n)`. The normalized presentation remains
noncomputable; these results are not an executable H-irrep classifier.

## 6. Scope and limitations

### Boundary

Vacuum selection, Yukawa invariance, anomaly cancellation, generated Wilson
coefficients, amplitudes and decay rates are not proved. In particular a
flavor action on this massless fermion sector is not asserted to preserve an
arbitrary specified Yukawa Lagrangian. The exterior theorem concerns algebraic
allowed coefficients, not inevitable proton decay.

The physical flavor-singlet observation overlaps with
[Alonso et al., section III.B](https://arxiv.org/abs/1405.0486).
This application verifies the repository's complete actual-source connection;
it does not claim that the SU(5) flavor-singlet observation is new.

See [the topic record](../../../../topics/georgi-glashow-exterior/README.md) for verification.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
