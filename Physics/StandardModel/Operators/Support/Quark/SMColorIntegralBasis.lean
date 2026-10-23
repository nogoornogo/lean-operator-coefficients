import Physics.StandardModel.Operators.Support.Coordinates.SMContentWeakBound
import Math.LieGroups.SpecialUnitary.ColorPlaneCircles

/-! Integral color-torus spanning on every actual signed statistical content. -/
namespace Physics.SMColorIntegralBasis
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor DeltaLOneSignedFields
open BoundedTorusWeights SMWeakWeightBasis
open scoped TensorProduct

def gaugeTorus : Circle →* GaugeGroup where
  toFun z := (ColorPlaneCircles.embedding 0 (TauCeti.SU2.torusHom z),(1,1))
  map_one' := by simp
  map_mul' _ _ := by simp

def colorWeight (i : Fin 3) : ℤ := if i=0 then 1 else if i=1 then -1 else 0

theorem color_basis_eigen (i : Fin 3) :
    Eigen color gaugeTorus (colorWeight i) (Pi.basisFun ℂ (Fin 3) i) := by
  intro z
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [color,gaugeTorus,ColorPlaneCircles.embedding_matrix,ColorPlaneCircles.planeMatrix,
      Pi.basisFun_apply,colorWeight,Matrix.toLin'_apply,Matrix.mulVec,
      TauCeti.SU2.coe_torusHom,TauCeti.SU2.torusMatrix]

theorem weak_basis_eigen (i : Fin 2) :
    Eigen weak gaugeTorus 0 (Pi.basisFun ℂ (Fin 2) i) := by
  intro z
  simp [weak,gaugeTorus,Matrix.toLin'_one]

theorem twist_eigen {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (y w : ℤ) (v : A)
    (hv : Eigen a gaugeTorus w v) : Eigen (twist a y) gaugeTorus w v := by
  intro z
  change phase y (gaugeTorus z) • a (gaugeTorus z) v = _
  have hp : phase y (gaugeTorus z) = 1 := by simp [phase,gaugeTorus]
  rw [hp,one_smul,hv z]

def gaugeWeight (s : DeltaLOneSignedInput.Species) : GaugeIndex s → ℤ := match s with
  | 0 => fun i => colorWeight i.1
  | 1 => colorWeight
  | 2 => colorWeight
  | 3 => fun _ => 0
  | 4 => fun _ => 0
  | 5 => fun i => -colorWeight i.1
  | 6 => fun i => -colorWeight i
  | 7 => fun i => -colorWeight i
  | 8 => fun _ => 0
  | 9 => fun _ => 0

theorem gauge_basis_eigen (s : DeltaLOneSignedInput.Species) (i : GaugeIndex s) :
    Eigen (gauge s) gaugeTorus (gaugeWeight s i) (gaugeBasis s i) := by
  have hq (i : Fin 3 × Fin 2) : Eigen quark gaugeTorus (colorWeight i.1) (quarkBasis i) := by
    rcases i with ⟨i,j⟩
    apply twist_eigen
    simpa [quarkBasis,Module.Basis.tensorProduct_apply] using
      eigen_tmul color gaugeTorus weak (color_basis_eigen i) (weak_basis_eigen j)
  have hu (i : Fin 3) : Eigen upRight gaugeTorus (colorWeight i) (Pi.basisFun ℂ (Fin 3) i) :=
    twist_eigen color 4 _ _ (color_basis_eigen i)
  have hd (i : Fin 3) : Eigen downRight gaugeTorus (colorWeight i) (Pi.basisFun ℂ (Fin 3) i) :=
    twist_eigen color (-2) _ _ (color_basis_eigen i)
  have hl (i : Fin 2) : Eigen lepton gaugeTorus 0 (Pi.basisFun ℂ (Fin 2) i) :=
    twist_eigen weak (-3) 0 _ (weak_basis_eigen i)
  have he (i : Fin 1) : Eigen electronRight gaugeTorus 0 (scalarBasis i) := by
    apply twist_eigen
    intro z
    simp
  fin_cases s
  · exact hq i
  · exact hu i
  · exact hd i
  · exact hl i
  · exact he i
  · exact dual_basis_eigen quark gaugeTorus quarkBasis _ hq i
  · exact dual_basis_eigen upRight gaugeTorus (Pi.basisFun ℂ (Fin 3)) _ hu i
  · exact dual_basis_eigen downRight gaugeTorus (Pi.basisFun ℂ (Fin 3)) _ hd i
  · simpa only [DeltaLOneSignedFields.gauge,gaugeWeight,gaugeBasis,neg_zero] using
      dual_basis_eigen lepton gaugeTorus (Pi.basisFun ℂ (Fin 2)) _ hl i
  · simpa only [DeltaLOneSignedFields.gauge,gaugeWeight,gaugeBasis,neg_zero] using
      dual_basis_eigen electronRight gaugeTorus scalarBasis _ he i

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def fullTorus : Circle →* NeutralHiggsPowers.G H where
  toFun z := ((gaugeTorus z,1),1)
  map_one' := by simp
  map_mul' _ _ := by simp

theorem field_basis_eigen (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) :
    Eigen (field flavor s) (fullTorus (H := H)) (gaugeWeight s i.1.1) (fieldBasis s i) := by
  rcases i with ⟨⟨i,j⟩,k⟩
  intro z
  simp only [fieldBasis,Module.Basis.tensorProduct_apply]
  change (field flavor s) (fullTorus (H := H) z)
    ((gaugeBasis s i ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin 2) j) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin 3) k) = _
  simp only [field,localField,ExternalInvariantTensor.external,fullTorus,
    Representation.tprod_apply,TensorProduct.map_tmul]
  change ((gauge s (gaugeTorus z) (gaugeBasis s i)) ⊗ₜ[ℂ]
    (FourSameWeylCompleteness.action (rightHanded s) 1 (Pi.basisFun ℂ (Fin 2) j))) ⊗ₜ[ℂ]
    (flavor s 1 (Pi.basisFun ℂ (Fin 3) k)) = _
  simp only [map_one,Module.End.one_apply]
  rw [gauge_basis_eigen s i z]
  simp only [← TensorProduct.smul_tmul']

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

@[reducible] local instance : AddCommGroup
    (⨂[ℂ] i : Fin n, DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) (p i)) :=
  inferInstance

theorem raw_basis_eigen (j : ∀ i, FieldIndex (p i)) :
    Eigen (PatternExteriorSource.Raw (field flavor) p) (fullTorus (H := H))
      (∑ i, gaugeWeight (p i) (j i).1.1) (SMContentWeakBound.tensorBasis p j) := by
  intro z
  rw [SMContentWeakBound.tensorBasis,Basis.piTensorProduct_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod]
  have hb (i : Fin n) := field_basis_eigen flavor (p i) (j i) z
  simp_rw [hb]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ,
    ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero]

theorem raw_integral : IntegralTorusTests.Integral (PatternExteriorSource.Raw (field flavor) p) (fullTorus (H := H)) :=
  IntegralTorusTests.of_basis (PatternExteriorSource.Raw (field flavor) p) (fullTorus (H := H))
    (SMContentWeakBound.tensorBasis p) (fun j => ∑ i, gaugeWeight (p i) (j i).1.1)
    (raw_basis_eigen flavor p)

theorem source_integral : IntegralTorusTests.Integral
    (SMContentWeakBound.source flavor p) (fullTorus (H := H)) :=
  IntegralTorusTests.of_surjective (PatternExteriorSource.Raw (field flavor) p) (fullTorus (H := H))
    (SMContentWeakBound.source flavor p) (PatternExteriorSource.onto (field flavor) p)
    (PatternExteriorSource.onto_surjective (field flavor) p) (raw_integral flavor p)

end
end Physics.SMColorIntegralBasis
