import Math.RepresentationTheory.Weights.BoundedTorusWeights
import Physics.StandardModel.Operators.Higgs.WeakSingletHiggsSupport
import Physics.StandardModel.Operators.Selection.ThreeGenerationFermionBound
import Mathlib.LinearAlgebra.Dual.Basis

/-! The actual signed SM gauge slots have weak weights 0 or plus/minus 1.
Flavor and Weyl slots do not change these weights. -/
namespace Physics.SMWeakWeightBasis
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor DeltaLOneSignedFields
open BoundedTorusWeights
open scoped TensorProduct

def gaugeTorus : Circle →* GaugeGroup where
  toFun z := (1,(TauCeti.SU2.torusHom z,1))
  map_one' := by simp
  map_mul' _ _ := by simp

def weakWeight (i : Fin 2) : ℤ := if i=0 then 1 else -1

theorem weak_basis_eigen (i : Fin 2) :
    Eigen weak gaugeTorus (weakWeight i) (Pi.basisFun ℂ (Fin 2) i) := by
  intro z
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [weak, gaugeTorus, Pi.basisFun_apply, weakWeight, Matrix.toLin'_apply,
      Matrix.mulVec, TauCeti.SU2.coe_torusHom,
      TauCeti.SU2.torusMatrix_apply_zero_zero, TauCeti.SU2.torusMatrix_apply_zero_one,
      TauCeti.SU2.torusMatrix_apply_one_zero, TauCeti.SU2.torusMatrix_apply_one_one]

theorem color_basis_eigen (i : Fin 3) :
    Eigen color gaugeTorus 0 (Pi.basisFun ℂ (Fin 3) i) := by
  intro z
  simp [color, gaugeTorus, Matrix.toLin'_one]

theorem twist_eigen {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : Representation ℂ GaugeGroup A) (y w : ℤ) (v : A)
    (hv : Eigen a gaugeTorus w v) : Eigen (twist a y) gaugeTorus w v := by
  intro z
  change phase y (gaugeTorus z) • a (gaugeTorus z) v = _
  have hp : phase y (gaugeTorus z) = 1 := by simp [phase, gaugeTorus]
  rw [hp, one_smul, hv z]

abbrev GaugeIndex : DeltaLOneSignedInput.Species → Type
  | 0 => Fin 3 × Fin 2
  | 1 => Fin 3
  | 2 => Fin 3
  | 3 => Fin 2
  | 4 => Fin 1
  | 5 => Fin 3 × Fin 2
  | 6 => Fin 3
  | 7 => Fin 3
  | 8 => Fin 2
  | 9 => Fin 1

instance (s : DeltaLOneSignedInput.Species) : Fintype (GaugeIndex s) := match s with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance
instance (s : DeltaLOneSignedInput.Species) : DecidableEq (GaugeIndex s) := match s with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance

def scalarBasis : Module.Basis (Fin 1) ℂ ℂ :=
  (Module.Basis.singleton (Fin 1) ℂ).reindex (Equiv.refl _)

def quarkBasis := (Pi.basisFun ℂ (Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin 2))

def gaugeBasis (s : DeltaLOneSignedInput.Species) : Module.Basis (GaugeIndex s) ℂ (GaugeCarrier s) :=
  match s with
  | 0 => quarkBasis
  | 1 => Pi.basisFun ℂ (Fin 3)
  | 2 => Pi.basisFun ℂ (Fin 3)
  | 3 => Pi.basisFun ℂ (Fin 2)
  | 4 => scalarBasis
  | 5 => quarkBasis.dualBasis
  | 6 => (Pi.basisFun ℂ (Fin 3)).dualBasis
  | 7 => (Pi.basisFun ℂ (Fin 3)).dualBasis
  | 8 => (Pi.basisFun ℂ (Fin 2)).dualBasis
  | 9 => scalarBasis.dualBasis

def gaugeWeight (s : DeltaLOneSignedInput.Species) : GaugeIndex s → ℤ := match s with
  | 0 => fun i => weakWeight i.2
  | 1 => fun _ => 0
  | 2 => fun _ => 0
  | 3 => weakWeight
  | 4 => fun _ => 0
  | 5 => fun i => -weakWeight i.2
  | 6 => fun _ => 0
  | 7 => fun _ => 0
  | 8 => fun i => -weakWeight i
  | 9 => fun _ => 0

def doubletCount (s : DeltaLOneSignedInput.Species) : ℕ :=
  if s=0 ∨ s=3 ∨ s=5 ∨ s=8 then 1 else 0

theorem gauge_basis_eigen (s : DeltaLOneSignedInput.Species) (i : GaugeIndex s) :
    Eigen (gauge s) gaugeTorus (gaugeWeight s i) (gaugeBasis s i) := by
  have hq (i : Fin 3 × Fin 2) : Eigen quark gaugeTorus (weakWeight i.2) (quarkBasis i) := by
    rcases i with ⟨i,j⟩
    apply twist_eigen
    simpa [quarkBasis, Module.Basis.tensorProduct_apply] using
      eigen_tmul color gaugeTorus weak (color_basis_eigen i) (weak_basis_eigen j)
  have hu (i : Fin 3) : Eigen upRight gaugeTorus 0 (Pi.basisFun ℂ (Fin 3) i) :=
    twist_eigen color 4 0 _ (color_basis_eigen i)
  have hd (i : Fin 3) : Eigen downRight gaugeTorus 0 (Pi.basisFun ℂ (Fin 3) i) :=
    twist_eigen color (-2) 0 _ (color_basis_eigen i)
  have hl (i : Fin 2) : Eigen lepton gaugeTorus (weakWeight i) (Pi.basisFun ℂ (Fin 2) i) :=
    twist_eigen weak (-3) _ _ (weak_basis_eigen i)
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
  · simpa only [DeltaLOneSignedFields.gauge, gaugeWeight, gaugeBasis, neg_zero] using
      dual_basis_eigen upRight gaugeTorus (Pi.basisFun ℂ (Fin 3)) _ hu i
  · simpa only [DeltaLOneSignedFields.gauge, gaugeWeight, gaugeBasis, neg_zero] using
      dual_basis_eigen downRight gaugeTorus (Pi.basisFun ℂ (Fin 3)) _ hd i
  · exact dual_basis_eigen lepton gaugeTorus (Pi.basisFun ℂ (Fin 2)) _ hl i
  · simpa only [DeltaLOneSignedFields.gauge, gaugeWeight, gaugeBasis, neg_zero] using
      dual_basis_eigen electronRight gaugeTorus scalarBasis _ he i

theorem gauge_weight_bound (s : DeltaLOneSignedInput.Species) (i : GaugeIndex s) :
    -(doubletCount s : ℤ) ≤ gaugeWeight s i ∧ gaugeWeight s i ≤ doubletCount s := by
  fin_cases s <;> simp [gaugeWeight, doubletCount, weakWeight] <;> split_ifs <;> omega

variable {H : Type*} [Group H]
def fullTorus : Circle →* NeutralHiggsPowers.G H :=
  (WeakSingletHiggsSupport.weakInclusion (H := H)).comp TauCeti.SU2.torusHom

abbrev FieldIndex (s : DeltaLOneSignedInput.Species) := (GaugeIndex s × Fin 2) × Fin 3
def fieldBasis (s : DeltaLOneSignedInput.Species) :
    Module.Basis (FieldIndex s) ℂ (Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  ((gaugeBasis s).tensorProduct (Pi.basisFun ℂ (Fin 2))).tensorProduct
    (Pi.basisFun ℂ (Fin 3))

theorem field_basis_eigen
    (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
    (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) :
    Eigen (field flavor s) fullTorus (gaugeWeight s i.1.1) (fieldBasis s i) := by
  rcases i with ⟨⟨i,j⟩,k⟩
  intro z
  simp only [fieldBasis, Module.Basis.tensorProduct_apply]
  change (field flavor s) (fullTorus z)
    ((gaugeBasis s i ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin 2) j) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin 3) k) = _
  simp only [field, localField, ExternalInvariantTensor.external, fullTorus,
    WeakSingletHiggsSupport.weakInclusion, MonoidHom.comp_apply,
    Representation.tprod_apply, TensorProduct.map_tmul]
  change ((DeltaLOneSignedFields.gauge s (gaugeTorus z) (gaugeBasis s i)) ⊗ₜ[ℂ]
    (FourSameWeylCompleteness.action (rightHanded s) 1 (Pi.basisFun ℂ (Fin 2) j))) ⊗ₜ[ℂ]
    (flavor s 1 (Pi.basisFun ℂ (Fin 3) k)) = _
  simp only [map_one, Module.End.one_apply]
  rw [gauge_basis_eigen s i z]
  simp only [← TensorProduct.smul_tmul']

theorem field_bounded
    (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
    (s : DeltaLOneSignedInput.Species) : Bounded (field flavor s) fullTorus (doubletCount s) :=
  of_basis _ _ (fieldBasis s) (fun i => gaugeWeight s i.1.1) _
    (field_basis_eigen flavor s) (fun i => gauge_weight_bound s i.1.1)

end
end Physics.SMWeakWeightBasis
