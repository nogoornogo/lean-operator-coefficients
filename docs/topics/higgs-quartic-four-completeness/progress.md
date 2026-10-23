# Proved milestones and completed endpoint

## Actual input, invariant candidates and quotient independence

[HiggsQuarticFourInput](../../../Physics/FieldTheory/Jets/HiggsQuarticFourInput.lean)
selects the entire actual grade (4,4), with the generated input's full
relation preimage. It proves membership and invariance of q1,q2,q3 under
every global covering-SM and actual Lorentz group element. The paired
canonical contraction gives internal invariance; a general metric-pairing
identity proves Lorentz invariance. No candidate-span premise is used to
define the whole-grade coefficient input.

[ColoredFourWaveEvaluation](../../../Math/Algebra/ColoredFourWaveEvaluation.lean)
generalizes the four-wave substitution to arbitrary field amplitudes.
[HiggsQuarticFourWaves](../../../Physics/FieldTheory/Jets/HiggsQuarticFourWaves.lean)
proves null, conserving waves annihilate the complete free Higgs differential
ideal and every divergence, on unbounded jets and arbitrary multipliers.

[HiggsQuarticFourSeparation](../../../Physics/FieldTheory/Jets/HiggsQuarticFourSeparation.lean)
uses three explicit configurations, with values on (q1,q2,q3):

| Configuration | q1 | q2 | q3 |
| --- | ---: | ---: | ---: |
| Transverse | 2 | 8 | 2 |
| First collinear ordering | 8 | 8 | 0 |
| Second collinear ordering | 0 | 8 | 8 |

Its inverse matrix gives actual quotient decoders. `candidateEquivalence`
proves that the entire image of the three-candidate span in the full EOM/IBP
quotient is equivalent to three complex coordinates; `candidate_dimension`
gives dimension 3. `independent_mod_relations` rejects every nontrivial
linear combination in the complete relation module. These replace the
earlier inadmissible raw probes for quotient separation. Individual wave
decoders are not asserted to be full-group invariant coefficients.

## Whole-grade upper control

[ColoredQuarticSource](../../../Math/Algebra/ColoredQuarticSource.lean)
proves source coverage for arbitrary independent labels and all 35 derivative
allocations. The colored Lorentz tensors retain their actual action; the
all-first-derivative word is reduced by an explicit divergence rather than
being assumed pair symmetric. Free EOM traces and the explicit contracted
IBP identities reduce every invariant coefficient to first-derivative metric
pair products.

[Internal controls](../../../Physics/FieldTheory/Jets/HiggsQuarticFourInternalControls.lean)
use actual global gauge elements. Their phase weights leave seven scalar
contractions; four checked rotation rows and the three candidate values
determine these seven values. Finite classification cases are separate
bounded modules.

[HiggsQuarticFourUpper](../../../Physics/FieldTheory/Jets/HiggsQuarticFourUpper.lean)
proves `evaluate_injective` on the entire admitted selected coefficient
space. [SelectedRelationExtension](../../../Math/RepresentationTheory/SelectedRelationExtension.lean)
extends a selected linear functional through its actual quotient image;
it makes no invariant-global-extension assertion. These proof modules pass the expanded strict
inventories and full aggregate gate recorded in [verification](verification.md).

## Finite moments and coefficient assembly

The colored pairing construction proves internal invariance for arbitrary
group elements. A finite ordered-moment identity supplies Lorentz invariance
on every colored word, and hence the entire grade. Conservation and nullness
give full unbounded relation annihilation independently of that identity.
The coordinate assembly has passed with the moment identities as explicit
helper parameters: the value matrix, normalized coefficients, both inverse
laws, dimension three and direct/generated agreement are proved.

All concrete moment tables and their bounded assemblies pass kernel
checking. The public module supplies these proofs internally: no caller
moment premise remains. The complete equivalence and expanded strict audit
pass. The [result](results.md) gives the coefficient values and proof structure.

## Literature preparation

The three pinned primary displays have been inspected. The full-relation
[Li reduction](../../../Physics/FieldTheory/Jets/HiggsQuarticFourLiRelations.lean)
has passed: every linear functional annihilating the full free EOM/IBP module
evaluates the native densities as (4q3,q1,q2-q1-q3). This does not assume a
global invariant extension. The selected-input consumers and independent per-paper queue pass after
the concrete coefficient theorem; [validation](literature-validation.md)
records all three native dictionaries and their limits.

## Settled endpoint

The frozen coefficient theorem and all three paper comparisons are complete
within their native free/gaugeless scope. Strict audits, full build and
repository gates pass. There is no remaining obligation inside the frozen
contract. Interacting/local-gauge, full SMEFT, Hermitian-coordinate and
global invariant-extension questions remain separate boundaries. This
completed topic is committed on its working branch; master integration and
remote updates require separate direction.
