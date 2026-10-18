# Physics Assumptions: Endpoint-Specific Inputs

[Ledger index](../ASSUMPTIONS.md). These are theorem-specific inputs, not a
universal hypothesis package. Recorded checks retain their topic checkpoints.

## Endpoint-Specific Inputs

### Abelian Charge Profiles

- H has `CommGroup H`; it need not be finite, torsion-free, or topological.
- The **whole T x H restriction** is unitary in the supplied inner product.
  Unitarity of the full ambient G action is not required by this core.
- Five finitely supported natural-valued charge profiles P describe
  Q, up, down, lepton and electron. Labels are actual circle-valued characters
  of H (in the repository's additive label convention), not just integers.
- `HasPartialTarget` prescribes the charge-resolved **dual index** at all
  fifteen oriented SM weights. Writing m for the actual radical multiplicity,
  the requirement is, for every monitored weight w_i and every charge q,
  `m(w_i,q) - m(-w_i,-q) = P_species(i)(q)`.
  The same species profile is used at every weight of that species.
- For the four-weight qque-only endpoint, `FourWeightQque.HasTarget` restricts
  this equation to 0, 3, 8, 14. The two Q slots share P_Q. The reused profile
  container's down/lepton entries impose no matching condition.
- Q total is positive for the qque-only endpoint. Q and down totals are
  separately positive for the pair. Their equality is not assumed.

`exists_supported_qque` uses the separate operator-local `SlotsSupported`
predicate. Legacy `ChargesSupported` checks all five species, including
down/lepton even for qque. Thus the Q-only theorem refutes the **slotwise**
universal prohibition, not the legacy full-support prohibition, which can
be vacuous with missing spectators. `selection_rule_obstruction` with positive
Q/down refutes the unchanged legacy predicate. See [support definitions](../../../../../../Physics/StandardModel/Operators/SlotSupport.lean).

### Finite Non-Abelian Targets

- H has `Group H` and `Fintype H` for the retained finite constituent-extraction
  and coefficient theorems. The compact continuous qque endpoint below is
  separate. Earlier character-transport lemmas need not assume H finite.
- Only the **T action** is required unitary in the supplied inner product.
  The endpoint does not separately require the H action or target actions
  to be unitary. Finite-group semisimplicity is used in extraction.
- Each P_s is an actual finite-dimensional complex H representation, not
  merely a dimension, charge list, or virtual signed target.
- `NonabelianSMTarget.Matches` requires, for every i and every h in H,
  `character(L_w_i)(h) - character((L_-w_i)*)(h) = character(P_species(i))(h)`.
  Here L_w is the actual weight space inside the mass radical and `*` is
  contragredient. This is representation-valued local index information,
  strictly more data than matching particle counts at h = 1.
- `FourWeightLightQque.HasTarget` imposes this same equation only at
  0, 3, 8, 14. Its reused finite-dimensional target family has no down/lepton
  matching or nonzero requirement. Species compatibility is still derived.
- P_Q is nonzero for qque. P_down must also be nonzero for the pair.
  No equality of Q/down dimensions is required.

See [the exact target definition](../../../../../../Physics/StandardModel/Spectrum/NonabelianSMTarget.lean)
and [source bridge results](../../../../../topics/nonabelian-light-source/results.md).
The Abelian recovery theorem identifies the two target descriptions on their
common actual unitary domain. It does not extend the finite non-Abelian
endpoint to every H or replace the infinite-Abelian theorem.

### Compact Continuous QQue

[CompactLightQque](../../../../../../Physics/StandardModel/Operators/CompactLightQque.lean)
uses the same four-weight target predicate and the same two actual conjugators.

- H is a compact topological group. It need not be finite or Abelian.
- The residual H action on E is jointly continuous. There is no topology or
  continuity assumption on G, j or the conjugators at this endpoint.
- Only T-unitarity is assumed in the original inner product. A unitary model
  for H and semisimplicity are derived from compactness and continuity; they
  do not change the mass or identify the original H action as unitary in that
  original inner product.
- The reused target carriers are complex normed spaces. Only P_Q is required
  finite-dimensional, nonzero and jointly continuous by this API. Q/up/e
  character compatibility is derived; no extra continuity premise on the
  unused down/lepton targets or on up/e is imposed. Ordinary finite-dimensional
  target families are included.
- Continuity on the actual mass radical, weight spaces and the algebraic
  opposite-weight dual is proved. Split light projections are outputs.
- A Borel structure is selected internally. No compact duql existence theorem
  or extension to arbitrary discontinuous abstract H representations is claimed.

A finite/discrete compatibility theorem discharges the two continuity premises
automatically on normed finite-dimensional carriers. The retained finite
algebraic theorem still accepts target carriers without analytic structure.

### Route A: Supplied SM Field Decomposition

The [SM x H tensor endpoint](../../../applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md) adds
`CompactExplicitSMTensor.Decomposition` to the compact source inputs:

- An SM-cover x H action on the original mass radical, agreeing with the
  original T x H action along the physical covering torus. Residual H agreement
  is a derived consequence of this compatibility.
- Q as a subrepresentation of that radical; right-handed up/electron as
  subrepresentations of its dual, not as left-chiral fields in the radical.
- Full SM x H equivalences with standard gauge representations tensored with
  L_0, L_3, L_8* and L_14*. Both Q equivalences concern the same Q field.

This additional decomposition is **not** inferred from local index matching.
In particular, extra light SM multiplets with overlapping monitored weights
need not satisfy it. No full-SM UV mass invariance or extension is inferred.
The nonzero residual coefficient is derived by the compact theorem; the
adapter does not assume that coefficient exists. Its output is a nonzero
SM x H invariant functional on these actual ordered light-field subspaces.

### Route A: Spinor And Exterior Extension

The [spinor/exterior endpoint](../../../applications/Physics/LORENTZ_EXTERIOR_QQUE.md) uses exactly those
compact-source and full-SM decomposition inputs. It constructs left and right
spinors using g and entrywise conjugate g in SL(2,C), including their invariant
epsilon pairings; these are definitions, not an extra existence certificate.
One derived Q projection is reused twice in a symmetric residual coefficient.
All 24 field permutations are then alternated on the direct sum of the actual
Q, up-right and electron-right spinor fields. The coefficient descends to the
fourth exterior power, stays invariant, and has a nonzero evaluation.

The proof derives the common quotient and splits from the source hypotheses;
they are not additional premises.
There is no added exchange-symmetry input or minimum of two generations. The
statement retains an ordered qque coefficient with nonzero alternating descent,
not merely an unspecified invariant on the sum. No general Lorentz-cover
identification is proved. Route A still takes its SM field decomposition as
input; the alternative below derives participating fields from species indices.

### Route B: Species-Index Connection

The [source-derived connection](../../../../../topics/full-sm-light-bridge/implementation.md)
is implemented by
[LightSMSpeciesQque](../../../../../../Physics/StandardModel/Operators/LightSMSpeciesQque.lean).
Its source inputs are the finite-dimensional E and G x H representation,
T-unitarity, symmetric T x H mass B and two conjugations described above.
H is a compact topological group. Write K for the **unchanged radical of B**.
The additional inputs are:

- A jointly continuous SM-cover x H action on the unchanged radical K,
  agreeing with the original action on the physical covering torus x H:
  `D : LightSMAction.Compatible j rho B` and `IsJointlyContinuous D.action`.
- Target actions `P_s` on complex normed spaces. Only `P_0` (Q) is required
  finite-dimensional, nonzero and jointly continuous. Independent continuity
  or nonzero premises for the other targets are not needed by this API.
- `FourWeightLightQque.HasTarget j rho B P`: the actual radical dual-index
  equations at weights 0, 3, 8, 14, including opposite-weight terms.
- Three residual character identities, for the left-handed gauge species
  `R = quark, upRight.dual, electronRight.dual`:
  `chi(Hom_SM(R,K)) - chi(Hom_SM(R.dual,K).dual) = chi(P_R)`.
  These hold for every h in H, not just as dimension equalities. They are
  `LightSMSpeciesIndex.HasTarget j rho B D P`, with the same P0/P1/P4 as in
  the four-weight input. Down/lepton species indices are not prescribed.

The compatible SM action and species identities do not follow from four-weight
matching alone. Preservation of K by a compatible continuous SM x H action
on E is a sufficient constructor for
the action input; invariance of the original mass under that action is a
stronger, optional constructor. Route B does not assume that full-SM mass
invariance, an SM action on all of E, or continuity of H on all of E.
Continuity on the actual multiplicity spaces and duals follows from D.

Concrete gauge irreducibility, multiplicity continuity, common quotients,
SM x H equivariant splittings and the actual field identifications are
derived. Set `M_Q = Hom_SM(quark,K)`, `M_up = Hom_SM(upRight.dual,K)` and
`M_electron = Hom_SM(electronRight.dual,K)`. The constructed identifications are
`Q = quark tensor M_Q`, `U = upRight tensor M_up.dual` and
`E_right = electronRight tensor M_electron.dual`, up to SM x H equivariant
linear equivalence. Q lies in K, while U and E_right lie in K.dual. The
conclusion includes an ordered qque coefficient with nonzero alternating
descent, not merely arbitrary exterior support. See
`LightSMSpeciesQque.exists_actual_alternation` and `exists_actual_exterior`.

This is an alternative sufficient-condition package, not a proved inclusion
between the two adapters. It permits extraction of participating isotypic
subspaces without identifying them with whole monitored weight spaces.
It requires neither a decomposition of the whole radical into these species
nor absence of extra fields. Extra fields must still respect both sets of
index equations. No statement about an arbitrary radical lacking these
inputs is made. The original connection task supplied no concrete ambient
source; the later [retained SU(5) benchmark](../../../applications/GUT/GEORGI_GLASHOW_QQUE.md) now derives
these inputs for its zero-mass fermion sector.

### Exact-Spectrum Entry To Route B

[ExactSMSpectrumQque](../../../../../../Physics/StandardModel/Operators/ExactSMSpectrumQque.lean)
retains route B's ambient representation, T-unitarity, symmetric T x H mass,
two conjugations and continuous compatible SM-cover x H action on K. Instead
of supplied targets or either index package, it assumes
`ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s` and `0 < n`.
This is an SM-equivariant linear equivalence, forgetting H, between K and n
copies of Q + upRight.dual + downRight.dual + lepton + electronRight.dual,
plus s trivial SM representations. It is a condition on the **whole actual
light spectrum**, not merely its signed index or total dimension.

H may act nontrivially on all multiplicities, including singlets. Canonical
targets are the actual SM intertwiner spaces with their induced H actions.
The exact spectrum gives their dimensions and vanishing opposite species.
It also gives dimension n at all fifteen SM weights and zero at their
opposites. At weights 0, 3, 8, 14, evaluation on concrete gauge eigenvectors
is proved to be an H-equivariant isomorphism onto the actual light sector.
Thus the four-weight equations hold for every h, not just at the identity.

Both `exists_actual_alternation` and `exists_actual_exterior` have no target,
target-continuity, species-index or four-weight premise. Their derivation
does not require n = 3 or multiple generations; n = 0 remains excluded from
the nonzero conclusion. This is a convenient, spectrally narrower sufficient
condition, not a replacement for route B with extra light fields. The later
[SU(5) benchmark](../../../applications/GUT/GEORGI_GLASHOW_QQUE.md) supplies a concrete source for this entry.
See [the original result and verification](../../../../../topics/exact-sm-spectrum-qque/results.md).

### Signed Virtual-Index Entry

[VirtualIndexQque](../../../../../../Physics/StandardModel/Operators/VirtualIndexQque.lean)
retains the compact-continuous compatible SM action on K and the structural
ambient/mass inputs. Instead of positive actual targets, it takes a finite
family S_i of pairwise inequivalent, continuous irreducible finite-dimensional
complex H representations on normed carriers, and integer profiles a_s(i).
Negative coefficients are permitted; only
`sum_i a_Q(i) * finrank(V_i) > 0` is required.

`VirtualSMSpeciesIndex.WeightMatches` and `SpeciesMatches` state the four
weight and three species equations with right sides `sum_i a_s(i) chi(S_i)`.
These are still character identities for every h, not just equal counts.
Two actual conjugations and T-unitarity derive equality of Q/up/e virtual
characters. Character pairing then extracts a common positive constituent;
split quotients, actual field identifications and nonzero alternating/exterior
descent are derived. No common quotient or coefficient is a premise.

The separate `exists_actual_alternation_of_common_index` entry takes equality
of those species virtual characters directly, without four-weight/conjugation
premises. Neither entry asserts exact SM particle content or arbitrary-index
compatibility. No anomaly or nonzero-amplitude condition is introduced.

In this retained API the normalized presentation is explicit input, not a
decomposition of the actual light space. The automatic species-index entry
below now constructs a presentation from actual representation differences.
Supplied actual targets with such a presentation
have nonnegative coefficients and positive dimension when nonzero, by proved
recovery lemmas. A complete automatic conversion of all old input packages
has not been proved. The Circle character 2-z is a checked positive-dimensional
signed control that cannot be an actual continuous representation's character;
it is not an end-to-end GUT source example. See [results and boundaries](../../../../../topics/virtual-index-qque/results.md).

### One Shared Positive Constituent

[SharedPositiveQque](../../../../../../Physics/StandardModel/Operators/SharedPositiveQque.lean)
keeps the same source carrier/mass interface and compatible continuous action
D on K as the signed virtual-index entry. Its inputs include the same finite
normalized family of continuous irreducibles and three species character
equations. In place of common characters and positive Q total dimension, it
requires `SharedPositiveSpeciesIndex.SharedPositive a`:
there exists i with `a_Q(i) > 0`, `a_up(i) > 0`, `a_electron(i) > 0`.
The coefficients need not be equal; the other coefficients and total
dimensions are unrestricted by this positivity predicate.

This direct species-index entry has no T-unitarity, four-weight matching or
two-conjugation premise. These are not silently derived. The continuous
compatible action on K and all three species equations remain required.
Common split quotients, actual subspaces and nonzero qque alternating/exterior
descent are outputs. Species indices are still identities for every h, not
merely positive particle counts.

`of_common_index` proves recovery from the previous common-character and
positive-dimension package in the same normalized family; `of_conjugations`
connects its old structural input package to the new local positivity condition.
This does not show that arbitrary unequal indices follow from the old matching
conditions. Circle controls demonstrate unequal indices and nonpositive totals
with shared positive support, not a new ambient-GUT benchmark. Normal-form
construction was outside that task and is now supplied by the automatic entry
below; dynamics remains excluded. The two-different-
constituent extension was outside that task's original scope and has since
been proved in the pairwise entry below.
See [results](../../../../../topics/shared-positive-qque/results.md).

### Two Pairwise Positive Constituents

[PairwisePositiveQque](../../../../../../Physics/StandardModel/Operators/PairwisePositiveQque.lean)
retains the shared-positive entry's source, compatible continuous action and
three normalized species equations. It replaces three-way shared support with
`PairwisePositiveSpeciesIndex.PairwisePositive a`: some i has positive Q/up
coefficients, and some k has positive Q/e coefficients. No relation between
i and k or the positive coefficient values is required. `of_shared` proves
recovery of the previous condition.

Four split maps are derived, and two evaluation pairings are symmetrized in
the repeated Q field. Their symmetric coefficient and its spinor/exterior
descent are proved nonzero without assuming orthogonal splits, zero cross
projections, exchange symmetry or extra generations. As in the direct shared
entry, no conjugations, four-weight matching, T-unitarity, whole-index equality
or positive total dimension are required. Species character equations and the
compatible SM action are not derived merely from pairwise support.

The Circle multiplicity example Q=1+z, up=1, e=z has pairwise but no three-way
positive support and a checked nonzero explicit field-model exterior coefficient.
It is not a constructed ambient-GUT source satisfying all radical inputs.
The theorem is sufficient, not a necessary criterion for qque to exist.
See [results and verification](../../../../../topics/pairwise-positive-qque/results.md).

### Automatic Species-Index Presentation

[AutomaticSpeciesQque](../../../../../../Physics/StandardModel/Operators/AutomaticSpeciesQque.lean)
retains the direct pairwise entry's ambient/mass carrier interface, compact H
and compatible jointly continuous SM-cover x H action D on K. It constructs
a common finite normalized irreducible family from the actual species
multiplicity representations and opposite-species duals. Their continuity,
irreducibility, pairwise inequivalence, signed coefficients and character
matching equations are proved, not additional input certificates.

Its sole additional support condition is
`AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd`: the constructed
profiles have positive Q/up overlap and positive Q/e overlap. Positivity
does not follow for arbitrary spectra. Coefficients are differences of
actual intertwiner-space dimensions, not an unrelated prescribed table.
All five standard species indices are constructed; no down/lepton positivity
or exact-spectrum condition is imposed. Conjugations, T-unitarity and
four-weight matching remain unnecessary for this direct entry.

The construction is noncomputable, not an executable classification algorithm.
It selects representatives without claiming a canonical order and may retain
zero-coefficient components. This removes input preparation, not the physical
need for positive support or compact-continuous actions. The supplied-family
APIs remain available; no universal comparison theorem for arbitrary
presentations is asserted. `ExactSMAutomaticPositive` now derives shared,
and hence pairwise, positivity from an exact positive-generation SM spectrum,
T-unitarity and two actual conjugations. The [retained SU(5) application](../../../applications/GUT/GEORGI_GLASHOW_QQUE.md)
constructs all of those inputs rather than assuming their availability.
See [construction and audits](../../../../../topics/normalized-virtual-presentation/results.md).

### Balanced Species Extension

[BalancedSpeciesQque](../../../../../../Physics/StandardModel/Operators/BalancedSpeciesQque.lean)
compares a new source to an exact-SM reference with the same H, but possibly
a different ambient group and mass. The reference requires positive
generations, T-unitarity and two actual conjugations. The new source requires
the standard ambient/mass carrier and compatible continuous SM-cover x H
action on its radical, with compact H; no exact spectrum or conjugators
are required on this new source.

For each of Q, up-left and electron-left, supply H-equivariant decompositions
of its actual multiplicity and its opposite-species dual as the corresponding
reference multiplicity plus the SAME additional H representation. The three
additional representations may differ. Their cancellation derives the species
character identities and shared/pairwise positive support in the new automatic
presentation. Neither positive support nor a nonzero coefficient is assumed.

These spectral decomposition certificates are real additional inputs to this
retained API, not consequences of matching SM particle counts. The global
vectorlike entrance below now constructs them and supplies a nonzero-extra
ambient example. The identity certificate recovers the exact
entrance; a positive Q addition conditionally excludes the old exact spectrum.
See [the full statement](../../../applications/Physics/BALANCED_SPECIES_EXTENSION.md).

### Global Vectorlike Spectrum

[VectorlikeSpectrumQque](../../../../../../Physics/StandardModel/Operators/VectorlikeSpectrumQque.lean)
keeps the two actual source/mass interfaces of the balanced extension. Instead
of three species decomposition certificates, it takes a finite-dimensional
continuous SM-cover x H representation X and one actual equivariant equivalence
`K = K0 + X + X.dual`. The dual includes both SM and H. The reference retains
its exact positive-generation spectrum, T-unitarity and actual conjugators.
The new radical has a compatible jointly continuous action, with compact H.

SM compactness and continuity of X supply semisimplicity; concrete gauge
irreducibility and a perfect intertwiner trace pairing supply H-equivariant
duality of multiplicities. All three balanced certificates and shared positive
support of the new actual normalized indices are derived, followed by the
nonzero actual exterior qque coefficient. No extra generation, index matching,
semisimplicity or constituent premise is imposed. The new source needs no
exact spectrum, T-unitarity or conjugators of its own. No independent
reference-continuity premise is required by this API.

The full spectrum equivalence remains an input, not something inferred from
SM-only particle counts or arbitrary masses. A concrete SU(5) zero-mass control
with two matter copies and one dual copy constructs the equivalence; its
extra Q multiplicity is positive and its spectrum is proved not to satisfy
the old exact-SM-plus-singlets predicate for any counts. Its H is trivial;
the general theorem is not so restricted. See [scope](../VECTORLIKE_SPECTRUM.md).
