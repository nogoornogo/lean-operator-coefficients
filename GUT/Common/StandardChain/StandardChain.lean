import GUT.SU5.SelectionRules.TorusMassSource
import Math.RepresentationTheory.Unitary.CommutingUnitaryActions
import Physics.FieldTheory.Yukawa.Mass.WeylMassFamily

open Physics

open Math

/-!
# The standard SU(5) chain in an arbitrary ambient group

Pullback along a supplied SU(5) homomorphism gives the common supported
selection-rule obstruction. Injectivity and continuity are separated into
the physically continuous wrapper; they are not used to prove the algebraic
pullback theorem. No classification of ambient embeddings is asserted.
-/

set_option autoImplicit false

namespace GUT.StandardChain

noncomputable section

open SU5 StandardModelEmbedding FiniteAbelianChargeSectors InvariantWeylMass
open StandardModelLocalOperator StandardSMCharacterTarget

variable {G H E : Type*} [Group G] [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def pullback (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E) :
    Representation ℂ (TargetGroup × H) E := rho.comp (i.prodMap (MonoidHom.id H))

def torusInclusion (i : TargetGroup →* G) : TorusCharacter.CombinedGroup H →* (G × H) :=
  (i.comp MaximalTorus.hom).prodMap (MonoidHom.id H)

omit [FiniteDimensional ℂ E] in
theorem restrict_pullback (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E) :
    TorusCharacterSource.restrict (pullback i rho) = rho.comp (torusInclusion i) := rfl

omit [FiniteDimensional ℂ E] in
theorem pullback_unitary (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    UnitaryMultiplicity.IsUnitaryRepresentation (pullback i rho) :=
  fun g x y => hu (i g.1, g.2) x y

omit [FiniteDimensional ℂ E] in
theorem pullback_comp {K : Type*} [Group K] (i : TargetGroup →* G) (j : G →* K)
    (rho : Representation ℂ (K × H) E) :
    pullback i (rho.comp (j.prodMap (MonoidHom.id H))) = pullback (j.comp i) rho := rfl

/-- The light dual target is an explicit IR hypothesis. Profile compatibility
and support are deliberately absent from the model fields. -/
structure Model (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E) where
  unitary : UnitaryMultiplicity.IsUnitaryRepresentation rho
  mass : SymmetricMass (rho.comp (torusInclusion i))
  profile : FiniteChargeProfiles.Family (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : TorusMassSource.HasTarget (pullback i rho) mass profile.profiles singlets

namespace Model

def ofSU5 (rho : Representation ℂ (TargetGroup × H) E)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (B : SymmetricMass (TorusCharacterSource.restrict rho))
    (F : FiniteChargeProfiles.Family (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : TorusMassSource.HasTarget rho B F.profiles s) :
    Model (MonoidHom.id TargetGroup) rho where
  unitary := hu
  mass := B
  profile := F
  singlets := s
  lightTarget := ht

variable {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E} (M : Model i rho)

def lightSpectrum :=
  TorusMassSource.spectrum (pullback i rho) (pullback_unitary i rho M.unitary) M.mass

theorem ofSU5_spectrum (rho : Representation ℂ (TargetGroup × H) E)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
    (B : SymmetricMass (TorusCharacterSource.restrict rho))
    (F : FiniteChargeProfiles.Family (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : TorusMassSource.HasTarget rho B F.profiles s) :
    (ofSU5 rho hu B F s ht).lightSpectrum = TorusMassSource.spectrum rho hu B := rfl

theorem profiles_compatible : FiniteChargeProfiles.OrbitCompatible M.profile.profiles :=
  TorusMassSource.profiles_compatible (pullback i rho) M.mass _ _ M.lightTarget

theorem actual_signature_pair :
    ∃ Q D : SupportedInvariantOperator M.lightSpectrum,
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ j : Fin 15, ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, M.mass.radical.toRepresentation g v =
          TorusCharacter.keyCharacter (smResolvedKey Q.charges j) g • v :=
  TorusMassSource.exists_actual_signature_pair (pullback i rho)
    (pullback_unitary i rho M.unitary) M.mass M.singlets M.profile M.lightTarget

theorem selection_rule_obstruction :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum :=
  TorusMassSource.selection_rule_obstruction (pullback i rho)
    (pullback_unitary i rho M.unitary) M.mass M.singlets M.profile M.lightTarget

end Model

section Continuity

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H]

/-- Physical admissibility of the supplied chain, without claiming that the
chosen VEV has exactly the SM stabilizer. -/
structure ContinuousModel (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E)
    extends Model i rho where
  inclusion_injective : Function.Injective i
  inclusion_continuous : Continuous i
  action_continuous : Continuous (fun p : (G × H) × E => rho p.1 p.2)

namespace ContinuousModel

variable {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E}
  (M : ContinuousModel i rho)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [FiniteDimensional ℂ E] in
include M in
theorem pullback_continuous :
    Continuous (fun p : (TargetGroup × H) × E => pullback i rho p.1 p.2) :=
  M.action_continuous.comp
    (((M.inclusion_continuous.comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem selection_rule_obstruction :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.toModel.lightSpectrum :=
  M.toModel.selection_rule_obstruction

end ContinuousModel

end Continuity

section ScalarFamily

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

/-- Scalar dependence may be nonlinear. The finite-dimensional fermion mass
is obtained by evaluating an equivariant family at a fixed vacuum. -/
structure ScalarModel (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E)
    (sigma : Representation ℂ (TorusCharacter.CombinedGroup H) S) where
  unitary : UnitaryMultiplicity.IsUnitaryRepresentation rho
  sector : WeylMassFamily.Sector sigma (rho.comp (torusInclusion i))
  family_continuous : Continuous (fun p : S × E × E => sector.family.toFun p.1 p.2.1 p.2.2)
  profile : FiniteChargeProfiles.Family (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : TorusMassSource.HasTarget (pullback i rho) sector.mass profile.profiles singlets

namespace ScalarModel

variable {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E}
  {sigma : Representation ℂ (TorusCharacter.CombinedGroup H) S} (M : ScalarModel i rho sigma)

def toMassModel : Model i rho where
  unitary := M.unitary
  mass := M.sector.mass
  profile := M.profile
  singlets := M.singlets
  lightTarget := M.lightTarget

def toContinuousMassModel [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (hi : Function.Injective i) (hc : Continuous i)
    (hr : Continuous (fun p : (G × H) × E => rho p.1 p.2)) : ContinuousModel i rho where
  toModel := M.toMassModel
  inclusion_injective := hi
  inclusion_continuous := hc
  action_continuous := hr

omit [FiniteDimensional ℂ E] in
@[simp] theorem toMassModel_form :
    M.toMassModel.mass.form = M.sector.bareMass.form +
      M.sector.family.toFun M.sector.vacuum.value := rfl

theorem selection_rule_obstruction :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.toMassModel.lightSpectrum :=
  M.toMassModel.selection_rule_obstruction

/-- Constant-family recovery preserves the mass exactly. -/
def ofMassModel (N : Model i rho) (sigma : Representation ℂ (TorusCharacter.CombinedGroup H) S) :
    ScalarModel i rho sigma where
  unitary := N.unitary
  sector := WeylMassFamily.Sector.ofBareMass N.mass
  family_continuous := continuous_const
  profile := N.profile
  singlets := N.singlets
  lightTarget := by
    simpa only [WeylMassFamily.Sector.ofBareMass_mass] using N.lightTarget

omit [FiniteDimensional ℂ E] in
@[simp] theorem ofMassModel_mass (N : Model i rho)
    (sigma : Representation ℂ (TorusCharacter.CombinedGroup H) S) :
    (ofMassModel N sigma).toMassModel.mass = N.mass :=
  WeylMassFamily.Sector.ofBareMass_mass N.mass

end ScalarModel

end ScalarFamily

end

end GUT.StandardChain
