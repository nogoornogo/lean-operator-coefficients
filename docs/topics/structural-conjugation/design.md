# Three Actual Conjugations: Design

Status: frozen implementation contract, now discharged; illustrative formulas
below are not a standalone Lean file. See the [proved statement](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md).
The [topic overview](README.md) owns progress, branch, stop gates and verification.

## Geometric Input

Keep the already faithful determinant-one torus T and the normalized SM weights.
Let `j : T ->* G` be a homomorphism to an arbitrary group G. For each of the
following permutations p, require a single element n_p in G satisfying

```text
forall t : T, j (permute p t) = n_p * j t * inverse n_p.
```

The element must work for every t; pointwise choices depending on t, numerical
checks, a lattice permutation alone, or a character equality supplied without
an actual conjugation are not this input. The witnesses need not themselves
form a homomorphism from a permutation group, satisfy Coxeter relations, or
have order two. Signed SU(5) representatives are allowed.

| Coordinate permutation (zero-based) | Existing normalized-weight identity | Needed equality |
| --- | --- | --- |
| `Equiv.swap (3 : Fin 5) 1` | `permuteReducedWeight_swap31_tenQ` | Q profile = up-conjugate profile |
| `Equiv.swap (0 : Fin 5) 4` | `permuteReducedWeight_swap04_tenQ` | Q profile = electron-conjugate profile |
| `Equiv.swap (0 : Fin 5) 3` | `permuteReducedWeight_swap03_barFiveDown` | down-conjugate profile = lepton profile |

These three suffice for the existing coefficient proof; no minimality claim
is made. Weight names containing `Ten` or `BarFive` label the existing SM
coordinate vectors, not a new premise about matter representations of G.

## Matter, Mass And Target

- H is any commutative group, including finite Abelian groups.
- E is a finite-dimensional complex inner-product space; rho is an actual
  unitary representation of `G x H` on E. This implements strict commuting
  gauge/residual actions. Conjugation by `(n_p, 1)` fixes H pointwise.
- Restrict along `j.prodMap (MonoidHom.id H)` to obtain sigma on `T x H`.
- B is `SymmetricMass sigma`: invariant symmetric bilinear mass on this
  restriction, not necessarily invariant under all of G.
- F is the existing positive common-total finite charge-profile family, and s
  is the existing singlet polynomial. Require the existing exact dual trace
  target, now for sigma and B:

```text
char(rad B)(x) - char((rad B).dual)(x)
  = eval(chiralDifference(targetWithSinglets F.profiles s))(x).
```

Do not assume an eigenbasis, a source Laurent model, full radical spectrum
equality, absence of vectorlike zero modes, profile compatibility, or supported
operator existence. The target is an IR hypothesis; this topic does not derive
it for every physical Lagrangian.

The core does not require j injective, continuity, compactness, or simplicity
of G, just as the existing algebraic ambient pullback does not. This is not a
claim that such data alone describe a complete physical GUT. In the existing
continuous standard-chain adapter, retain its actual continuous injective
SU(5) inclusion, physical SM compatibility and continuity inputs unchanged.
T is the fixed SM weight-coordinate model; arbitrary SM embeddings or torus
identifications are not automatically covered.

## Derivation And Reuse Map

1. Apply `CharacterRestriction.character_restriction_invariant` separately
   to each `(n_p, 1)`. Obtain actual restricted trace and dual-trace invariance.
2. Use `B.radical_dual_character_eq` to move the light dual target to the
   source. The radical need not be preserved by n_p, so do not assert its
   full character is invariant.
3. Use `TorusCharacter.eval_injective` and `eval_permute` to derive invariance
   of the target polynomial under each selected permutation.
4. Extract single-permutation coefficient lemmas from `ChargeResolved`, and
   combine with `ProfileChiralIndex.chiralDifference_target_profile` to obtain
   `FiniteChargeProfiles.OrbitCompatible F.profiles`.
5. Reuse `AbelianMassSpectrum` and the target coefficient positivity results
   to obtain the actual resolved radical spectrum, its dual difference and
   nonzero joint eigenvectors at occupied SM weights.
6. Reuse `exists_occupied_trivial_characters`, `supportedQque`, `supportedDuql`
   and `SupportedInvariantOperator` to recover the existing signature-pair
   statement and negate `ForbidsEverySupportedPhysicalDeltaBOneOperator`.

Relevant sources (existing declaration namespaces remain compatible):

- [General trace/conjugation API](../../../Math/RepresentationTheory/Characters/CharacterRestriction.lean)
- [Faithful evaluator](../../../Physics/StandardModel/Spectrum/TorusCharacter.lean)
- [Three coordinate identities and coefficient proof](../../../Physics/StandardModel/Spectrum/ChargeResolved.lean)
- [Dual target and profiles](../../../Physics/StandardModel/Spectrum/ProfileChiralIndex.lean)
- [Actual mass spectrum](../../../Physics/FieldTheory/Mass/AbelianMassSpectrum.lean)
- [Current SU(5) source](../../../GUT/SU5/Branching/TorusCharacterSource.lean)
- [Current mass consumer](../../../GUT/SU5/SelectionRules/TorusMassSource.lean)
- [Ambient models](../../../GUT/Common/StandardChain/StandardChain.lean)

## Placement And Compatibility

Use the existing Math conjugation API without duplicating its proof. Add the
fixed-SM-coordinate criterion and mass endpoint under
`Physics/StandardModel/Spectrum/`, with persistent audits there. Preserve
Math -> no Physics/GUT and Physics -> no GUT application imports.

Place the concrete SU(5)-chain adapter under `GUT/Common/StandardChain/`.
Given `i : SU(5) ->* G`, take `j = i.comp MaximalTorus.hom` and
`n_p = i (MonomialElements.signedPermutation p)`. Prove the conjugation identity
from `MaximalTorus.hom_conjugate` and homomorphism laws. This constructs the
required witnesses rather than assuming the criterion for known groups.

Compare the restricted representations and actual radical spectra with the
existing `StandardChain.Model` and `TorusMassSource.spectrum`. Preserve the
same matter, mass, profile and singlet data. Existing SU(N)/Spin/E6-candidate
instances should be inherited through that adapter, not reimplemented.

## Controls And Audit Questions

- Positive: construct the SU(5)-chain witnesses and recover existing endpoints
  and actual spectra, including the nonempty SU(5) benchmark.
- Negative: the actual lepton-triality source forbids every supported signature.
  Prove that no extension reproducing its restricted action/target can satisfy
  all three conjugation hypotheses and the retained mass inputs. This is not
  a claim that its torus, by itself, has no embedding into any larger group.
- Check the permutation/inverse convention, all-left charge signs, singlet
  cancellation, nonempty actual support, and preservation of finite H cases.
- Check that neither full Weyl invariance nor the desired profile equalities
  are fields of the geometric/source interface, and that B is not silently
  required to be invariant under n_p.
- Reject unexpected transitive axioms and GUT imports in the general core;
  retain existing audit exclusions after any helper extraction.

## Interpretation Gate

Successful implementation establishes a sufficient structural criterion, not
that every GUT has these conjugations or that the criterion is necessary.
Recovering only known SU(5)-chain examples is a valid bounded endpoint, but
must be reported as structural repackaging, not demonstrated new physical
coverage. A proof of strictly wider applicability, a new non-SU(5) model,
or a literature novelty comparison is not silently added to this proof task.
