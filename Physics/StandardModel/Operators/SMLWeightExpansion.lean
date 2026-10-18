import Physics.StandardModel.Operators.SMConstantSourceCharacter
import Physics.StandardModel.Operators.SMLCompactWeyl
import Math.RepresentationTheory.SU2SignedWeights

/-! Uniform finite signed weights for the actual L exterior source. -/
namespace GUT.SMLWeightExpansion
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped BigOperators

abbrev Slots := SMWeakWeightBasis.FieldIndex (3 : DeltaLOneSignedInput.Species)
abbrev Subsets (n : ℕ) := Set.powersetCard Slots n

def weakWeight {n : ℕ} (s : Subsets n) : ℤ :=
  ∑ i ∈ (s : Finset Slots), SMWeakWeightBasis.weakWeight i.1.1

def spinWeight {n : ℕ} (s : Subsets n) : ℤ :=
  ∑ i ∈ (s : Finset Slots), SMWeakWeightBasis.weakWeight i.1.2

theorem prod_zpow {J : Type*} (s : Finset J) (a : J → ℤ) (z : Circle) :
    (∏ i ∈ s, (z : ℂ)^(a i)) = (z : ℂ)^(∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ z.coe_ne_zero]

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

local instance fieldFinite (s : DeltaLOneSignedInput.Species) :
    FiniteDimensional ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field, ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

local instance sourceFinite (n : ℕ) : FiniteDimensional ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n)) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n)).toLinearMap)
  infer_instance

theorem source_character (n : ℕ) (z w : Circle) :
    (SMLCompactWeyl.source flavor n).character (SMConstantSourceCharacter.leptonTorus z w) =
      ∑ s : Subsets n, (z : ℂ)^weakWeight s * (w : ℂ)^spinWeight s := by
  rw [SMConstantSourceCharacter.lepton_character, ExteriorCharacterPolynomial.generating_coeff]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib]
  rw [prod_zpow, prod_zpow]
  rfl

abbrev Indices (n m : ℕ) := Subsets n × Fin (m+1)
def totalWeak (n m : ℕ) (i : Indices n m) : ℤ := weakWeight i.1 + (2*(i.2 : ℤ)-m)
def totalSpin (n m : ℕ) (i : Indices n m) : ℤ := spinWeight i.1

def pairInclusion : (TauCeti.SU2 × TauCeti.SU2) →* NeutralHiggsPowers.G H where
  toFun k := (((1,(k.1,1)), SL2SymmetricEmbeddings.compactInclusion k.2),1)
  map_one' := by simp
  map_mul' _ _ := by simp

abbrev action (n m : ℕ) (delta : ℤ) : Representation ℂ (TauCeti.SU2 × TauCeti.SU2)
    (SMFullLocalKernel.Carrier flavor (SMLCompactWeyl.pattern n) m) :=
  (SMWeylFiniteKernel.fullAction flavor (SMLCompactWeyl.pattern n) m delta).comp pairInclusion

theorem torus_character (n m : ℕ) (delta : ℤ) (z w : Circle) :
    (action flavor n m delta).character (TauCeti.SU2.torusHom z, TauCeti.SU2.torusHom w) =
      ∑ i : Indices n m, (z : ℂ)^totalWeak n m i * (w : ℂ)^totalSpin n m i := by
  have hg : pairInclusion (H := H) (TauCeti.SU2.torusHom z, TauCeti.SU2.torusHom w) =
      SMConstantSourceCharacter.leptonTorus z w := rfl
  change (SMWeylFiniteKernel.fullAction flavor (SMLCompactWeyl.pattern n) m delta).character
    (pairInclusion (TauCeti.SU2.torusHom z, TauCeti.SU2.torusHom w)) = _
  rw [hg, Representation.char_tensor, Pi.mul_apply, source_character]
  have hb : (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta).character (SMConstantSourceCharacter.leptonTorus z w) =
      ∑ j : Fin (m+1), (z : ℂ)^(2*(j : ℤ)-m) := by
    rw [Representation.char_charTwist]
    have hh : SMHiggsConstituents.character (H := H)
        (SMConstantSourceCharacter.leptonTorus z w) = 1 := by
      apply Units.ext
      simp [SMHiggsConstituents.character_apply, SMConstantSourceCharacter.leptonTorus,
        StandardSMGaugeTensor.phase, SMWeakWeightBasis.gaugeTorus]
    have hpow : ((SMHiggsConstituents.character (H := H) ^ delta)
        (SMConstantSourceCharacter.leptonTorus z w) : ℂ) = 1 := by
      rw [MonoidHom.zpow_apply, hh]
      simp
    rw [hpow, one_mul]
    change (WeakDoubletScalars.doublet.symmetricPower m).character (TauCeti.SU2.torusHom z) = _
    rw [WeakDoubletScalars.symmetricPower_eq, TauCeti.SU2.character_symPower_torusHom_zpow]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [hb, Finset.sum_mul_sum]
  simp only [Fintype.sum_prod_type, totalWeak, totalSpin, zpow_add₀ z.coe_ne_zero]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end GUT.SMLWeightExpansion
