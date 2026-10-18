import Physics.StandardModel.Operators.SMComputableSlotWeights
import Physics.StandardModel.Operators.SMWeylExtractionInput
import Math.RepresentationTheory.ComputableWeightPolynomial

/-! Computable reference weights with an actual inverse-character presentation. -/
namespace GUT.SMComputableCharacter
set_option autoImplicit false
open Math Representation SMCompactTorus SMComputableSlotWeights
open ComputableWeightPolynomial
open scoped TensorProduct

def gaugeSize (s : DeltaLOneSignedInput.Species) : ℕ := ![6,3,3,2,1,6,3,3,2,1] s
def gaugeEquiv (s : DeltaLOneSignedInput.Species) : SMWeakWeightBasis.GaugeIndex s ≃ Fin (gaugeSize s) :=
  match s with
  | 0 => finProdFinEquiv | 1 => Equiv.refl _ | 2 => Equiv.refl _ | 3 => Equiv.refl _
  | 4 => Equiv.refl _ | 5 => finProdFinEquiv | 6 => Equiv.refl _ | 7 => Equiv.refl _
  | 8 => Equiv.refl _ | 9 => Equiv.refl _
def size (s : DeltaLOneSignedInput.Species) := (gaugeSize s * 2) * 3
def indexEquiv (s : DeltaLOneSignedInput.Species) : SMWeakWeightBasis.FieldIndex s ≃ Fin (size s) :=
  (Equiv.prodCongr ((Equiv.prodCongr (gaugeEquiv s) (Equiv.refl (Fin 2))).trans finProdFinEquiv)
    (Equiv.refl (Fin 3))).trans finProdFinEquiv
def slotWeight (s : DeltaLOneSignedInput.Species) (i : Fin (size s)) : Weight :=
  fieldWeight s ((indexEquiv s).symm i)
def exteriorTerms (s : DeltaLOneSignedInput.Species) (n : ℕ) : Terms Weight :=
  exterior (List.ofFn (fun i => -slotWeight s i)) n
def sourceTerms (c : DeltaLOneSignedInput.Species → ℕ) : Terms Weight :=
  product (List.ofFn (fun s => exteriorTerms s (c s)))
def bosonWeight (m : ℕ) (delta : ℤ) (j : Fin (m+1)) : Weight :=
  ![0,0,TauCeti.SU2.weight m j,0,0,3*delta]
def bosonTerms (m : ℕ) (delta : ℤ) : Terms Weight :=
  List.ofFn (fun j => (-bosonWeight m delta j,1))
def terms (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : Terms Weight :=
  multiply (sourceTerms c) (bosonTerms m delta)
def multiplicity (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : ℤ :=
  CompactWeylExtraction.constantTerm roots (coefficient (terms c m delta))

noncomputable section

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group :=
  borel SMCombinedCompactAction.Group
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

def slotBasis (s : DeltaLOneSignedInput.Species) :=
  (SMWeakWeightBasis.fieldBasis s).reindex (indexEquiv s)

theorem slot_eigen (s : DeltaLOneSignedInput.Species) (i : Fin (size s)) (t : Torus) :
    SMCombinedCompactAction.field s ((inclusion t)⁻¹) (slotBasis s i) =
      monomial (-slotWeight s i) t • slotBasis s i := by
  rw [← map_inv]
  simpa [slotBasis,Module.Basis.reindex_apply,slotWeight,monomial_inverse] using
    field_eigen s ((indexEquiv s).symm i) t⁻¹

local instance fieldFinite (s : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field,ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

theorem exterior_evaluation (s : DeltaLOneSignedInput.Species) (n : ℕ) (t : Torus) :
    evaluate (fun w => monomial w t) (exteriorTerms s n) =
      ((SMCombinedCompactAction.field s).exteriorPower n).character ((inclusion t)⁻¹) := by
  rw [exteriorTerms,exterior_ofFn_evaluate _ (monomial_zero t) (fun a b => monomial_add a b t)]
  exact (ExteriorCharacterPolynomial.exterior_character _ (slotBasis s) _ _
    (fun i => slot_eigen s i t) n).symm

def leaves (c : DeltaLOneSignedInput.Species → ℕ) (s : DeltaLOneSignedInput.Species) :
    ExteriorContentTree.Leaf SMCombinedCompactAction.Group where
  Carrier := DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s
  rho := SMCombinedCompactAction.field s
  degree := c s

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

local instance sourceFinite : FiniteDimensional ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) p).toLinearMap)
  infer_instance

theorem source_evaluation (t : Torus) :
    evaluate (fun w => monomial w t) (sourceTerms (SMIteratedContent.counts p)) =
      (SMCombinedCompactAction.source flavor p).character ((inclusion t)⁻¹) := by
  rw [sourceTerms,evaluate_product _ (monomial_zero t) (fun a b => monomial_add a b t),
    List.map_ofFn,List.prod_ofFn]
  simp only [Function.comp_apply,exterior_evaluation]
  exact (IndexedExteriorContent.word_character 9 (leaves (SMIteratedContent.counts p)) p
    (fun _ => rfl) (fun s => fieldFinite s) _).symm

theorem monomial_boson (m : ℕ) (delta : ℤ) (j : Fin (m+1)) (t : Torus) :
    monomial (bosonWeight m delta j) t =
      (t 5 : ℂ)^(3*delta) * (t 2 : ℂ)^TauCeti.SU2.weight m j := by
  simp [monomial,CircleTorusCharacterLattice.torusCharacter_apply,bosonWeight,
    Fin.prod_univ_succ,mul_comm]

theorem boson_character (m : ℕ) (delta : ℤ) (t : Torus) :
    (SMCombinedCompactAction.boson (H := H) m delta).character (inclusion t) =
      ∑ j : Fin (m+1), monomial (bosonWeight m delta j) t := by
  rw [show (SMCombinedCompactAction.boson (H := H) m delta).character (inclusion t) =
    (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta).character
        (SMCombinedCompactAction.gaugeEmbedding (inclusion t)) from rfl]
  rw [Representation.char_charTwist]
  have hp : (((SMHiggsConstituents.character (H := H)^delta)
      (SMCombinedCompactAction.gaugeEmbedding (inclusion t)) : ℂˣ) : ℂ) = (t 5 : ℂ)^(3*delta) := by
    have hc : ((SMHiggsConstituents.character (H := H)
        (SMCombinedCompactAction.gaugeEmbedding (inclusion t)) : ℂˣ) : ℂ) = (t 5 : ℂ)^(3 : ℤ) := by
      rfl
    rw [MonoidHom.zpow_apply,Units.val_zpow_eq_zpow_val,hc,← zpow_mul]
  rw [hp]
  change (t 5 : ℂ)^(3*delta) *
    (WeakDoubletScalars.doublet.symmetricPower m).character (TauCeti.SU2.torusHom (t 2)) = _
  rw [WeakDoubletScalars.symmetricPower_eq,TauCeti.SU2.character_symPower_torusHom_zpow,
    ← Fin.sum_univ_eq_sum_range]
  simp only [Finset.mul_sum,monomial_boson,TauCeti.SU2.weight]

theorem boson_evaluation (m : ℕ) (delta : ℤ) (t : Torus) :
    evaluate (fun w => monomial w t) (bosonTerms m delta) =
      (SMCombinedCompactAction.boson (H := H) m delta).character ((inclusion t)⁻¹) := by
  rw [← map_inv,boson_character]
  simp only [bosonTerms,evaluate,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    Int.cast_one,one_mul,monomial_inverse]

theorem terms_evaluation (m : ℕ) (delta : ℤ) (t : Torus) :
    evaluate (fun w => monomial w t) (terms (SMIteratedContent.counts p) m delta) =
      (SMCombinedCompactContinuity.model flavor p m delta).character ((inclusion t)⁻¹) := by
  calc
    _ = evaluate (fun w => monomial w t) (sourceTerms (SMIteratedContent.counts p)) *
        evaluate (fun w => monomial w t) (bosonTerms m delta) :=
      evaluate_multiply _ (fun a b => monomial_add a b t) _ _
    _ = (SMCombinedCompactAction.source flavor p).character ((inclusion t)⁻¹) *
        (SMCombinedCompactAction.boson (H := H) m delta).character ((inclusion t)⁻¹) :=
      congrArg₂ (fun x y : ℂ => x*y) (source_evaluation flavor p t) (boson_evaluation (H := H) m delta t)
    _ = (SMCombinedCompactAction.action flavor p m delta).character ((inclusion t)⁻¹) :=
      (congrFun (Representation.char_tensor (SMCombinedCompactAction.source flavor p)
        (SMCombinedCompactAction.boson (H := H) m delta)) ((inclusion t)⁻¹)).symm
    _ = _ := congrFun (Representation.char_iso (SMCombinedCompactContinuity.equiv flavor p m delta))
      ((inclusion t)⁻¹)

def polynomial (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) : Weight →₀ ℤ :=
  presentation (terms c m delta)


theorem polynomial_coefficient (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) (w : Weight) :
    polynomial c m delta w = coefficient (terms c m delta) w :=
  presentation_apply _ _

theorem extraction_eq (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) (delta : ℤ) :
    CompactWeylExtraction.constantTerm roots (polynomial c m delta) = multiplicity c m delta := by
  congr 1
  funext w
  exact polynomial_coefficient c m delta w

end
end GUT.SMComputableCharacter
