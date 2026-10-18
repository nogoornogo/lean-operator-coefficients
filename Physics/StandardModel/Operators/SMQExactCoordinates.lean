import Physics.StandardModel.Operators.SMRationalLocalKernel
import Physics.StandardModel.Operators.SMConstantContentRanks
import Physics.StandardModel.Operators.SMWeakWeightBasis
import Math.LinearAlgebra.ExactPowerCoordinates
import Math.RepresentationTheory.ConstantExteriorAction
import Physics.StandardModel.Operators.SMGaussianLocalData

/-! A finite explicit exterior/monomial basis for constant Q contents. -/
namespace GUT.SMQExactCoordinates
set_option autoImplicit false
noncomputable section
open Math Representation GaussianRational
open scoped TensorProduct

abbrev Slots := SMWeakWeightBasis.FieldIndex (0 : DeltaLOneSignedInput.Species)

def slotEquiv : Slots ≃ Fin 36 :=
  (((finProdFinEquiv.prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv).prodCongr
    (Equiv.refl (Fin 3))).trans finProdFinEquiv

def fieldBasis := (SMWeakWeightBasis.fieldBasis (0 : DeltaLOneSignedInput.Species)).reindex slotEquiv

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev pattern (n : ℕ) := SMConstantContentRanks.pattern 0 n
abbrev Index (n m : ℕ) := Set.powersetCard (Fin 36) n × Sym (Fin 2) m

def transport (n m : ℕ) :
    ((⋀[ℂ]^n (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) 0)) ⊗[ℂ]
      Sym[ℂ]^m WeakDoubletScalars.Doublet) ≃ₗ[ℂ] SMFullLocalKernel.Carrier flavor (pattern n) m :=
  TensorProduct.congr (ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n)
    (LinearEquiv.refl ℂ _)

def basis (n m : ℕ) : Module.Basis (Index n m) ℂ (SMFullLocalKernel.Carrier flavor (pattern n) m) :=
  ((fieldBasis.exteriorPower n).tensorProduct ((Pi.basisFun ℂ (Fin 2)).symmetricPower m)).map
    (transport flavor n m)

theorem field_coordinate (g : SMIntegralLocalWeights.Group) (i j : Slots) :
    (SMWeakWeightBasis.fieldBasis 0).repr
      (DeltaLOneSignedFields.field flavor 0 (g,1) (SMWeakWeightBasis.fieldBasis 0 i)) j =
      StandardSMGaugeTensor.phase 1 g.1 *
        (g.1.1 : Matrix (Fin 3) (Fin 3) ℂ) j.1.1.1 i.1.1.1 *
        (g.1.2.1 : Matrix (Fin 2) (Fin 2) ℂ) j.1.1.2 i.1.1.2 *
        (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j.1.2 i.1.2 * (if j.2=i.2 then 1 else 0) := by
  rcases i with ⟨⟨⟨a,b⟩,c⟩,d⟩
  rcases j with ⟨⟨⟨e,f⟩,h⟩,k⟩
  simp [SMWeakWeightBasis.fieldBasis, SMWeakWeightBasis.gaugeBasis, SMWeakWeightBasis.quarkBasis,
    DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField, DeltaLOneSignedFields.rightHanded,
    ExternalInvariantTensor.external, Representation.tprod_apply,
    StandardSMGaugeTensor.quark, StandardSMGaugeTensor.twist, StandardSMGaugeTensor.color,
    StandardSMGaugeTensor.weak, FourSameWeylCompleteness.action, WeylSpinor.left,
    Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
    Matrix.mulVec_single, Pi.single_apply, TensorProduct.map_tmul, mul_comm, mul_left_comm, mul_assoc]

def fieldMatrix (d : SMGaussianLocalData.Data) : Matrix (Fin 36) (Fin 36) Scalar := fun j i =>
  let a := slotEquiv.symm i
  let b := slotEquiv.symm j
  d.phase * d.color b.1.1.1 a.1.1.1 * d.weak b.1.1.2 a.1.1.2 * d.spin b.1.2 a.1.2 *
    (if b.2=a.2 then 1 else 0)

theorem field_sample_coordinate (n : ℕ) (t : SMRationalLocalKernel.Index n) (i j : Fin 36) :
    fieldBasis.repr (DeltaLOneSignedFields.field flavor 0 (SMRationalLocalKernel.tests n t,1)
      (fieldBasis i)) j = embed (fieldMatrix (SMGaussianLocalData.data n t) j i) := by
  unfold fieldBasis
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  rw [field_coordinate]
  dsimp only [fieldMatrix]
  simp only [map_mul, apply_ite, map_one, map_zero]
  have hc := congrFun (congrFun (SMGaussianLocalData.color_embed n t)
    (slotEquiv.symm j).1.1.1) (slotEquiv.symm i).1.1.1
  have hw := congrFun (congrFun (SMGaussianLocalData.weak_embed n t)
    (slotEquiv.symm j).1.1.2) (slotEquiv.symm i).1.1.2
  have hs := congrFun (congrFun (SMGaussianLocalData.spin_data_embed n t)
    (slotEquiv.symm j).1.2) (slotEquiv.symm i).1.2
  simp only [Matrix.map_apply] at hc hw hs
  rw [SMGaussianLocalData.phase_embed, hc, hw, hs]
  have hp : StandardSMGaugeTensor.phase 1 (SMRationalLocalKernel.tests n t).1 =
      ((SMRationalLocalKernel.tests n t).1.2.2 : ℂ) := by
    change (((SMRationalLocalKernel.tests n t).1.2.2 ^ (1 : ℤ) : Circle) : ℂ) = _
    rw [Circle.coe_zpow, zpow_one]
  rw [hp]
  split_ifs <;> rfl

def bosonMatrix (m : ℕ) (delta : ℤ) (d : SMGaussianLocalData.Data) :
    Matrix (Sym (Fin 2) m) (Sym (Fin 2) m) Scalar := fun s t =>
  d.phase^(3*delta) * ExactPowerCoordinates.symmetricFormula m d.weak s t

theorem boson_sample_coordinate (n m : ℕ) (delta : ℤ) (t : SMRationalLocalKernel.Index n)
    (s u : Sym (Fin 2) m) :
    ((Pi.basisFun ℂ (Fin 2)).symmetricPower m).repr
      (SMIntegralLocalWeights.boson (H := H) m delta (SMRationalLocalKernel.tests n t)
        ((Pi.basisFun ℂ (Fin 2)).symmetricPower m u)) s =
      embed (bosonMatrix m delta (SMGaussianLocalData.data n t) s u) := by
  let g := SMRationalLocalKernel.tests n t
  let d := SMGaussianLocalData.data n t
  have hc : ((SMHiggsConstituents.character (H := H)^delta) (g,1) : ℂ) =
      embed (d.phase^(3*delta)) := by
    rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
    change ((StandardSMGaugeTensor.phase 3 g.1)^delta) = _
    have hp : StandardSMGaugeTensor.phase 3 g.1 = (g.1.2.2 : ℂ)^(3 : ℤ) := by
      change ((g.1.2.2 ^ (3 : ℤ) : Circle) : ℂ) = _
      exact Circle.coe_zpow _ _
    rw [hp, map_zpow₀, SMGaussianLocalData.phase_embed, zpow_mul]
  change ((Pi.basisFun ℂ (Fin 2)).symmetricPower m).repr
    (((SMHiggsConstituents.character (H := H)^delta) (g,1) : ℂ) •
      (WeakDoubletScalars.doublet.symmetricPower m) g.1.2.1
        ((Pi.basisFun ℂ (Fin 2)).symmetricPower m u)) s = _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
  have hw := ExactPowerCoordinates.symmetric_map m d.weak s u
  have he : (d.weak.map embed) = (g.1.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    SMGaussianLocalData.weak_embed n t
  rw [he] at hw
  change _ * ((Pi.basisFun ℂ (Fin 2)).symmetricPower m).repr
    (SymmetricPower.map (Matrix.toLin' (g.1.2.1 : Matrix (Fin 2) (Fin 2) ℂ))
      ((Pi.basisFun ℂ (Fin 2)).symmetricPower m u)) s = _
  calc
    _ = embed (d.phase^(3*delta)) * embed (ExactPowerCoordinates.symmetricMatrix m d.weak s u) :=
      congrArg (fun z : ℂ => embed (d.phase^(3*delta)) * z) hw
    _ = _ := by
      simp only [bosonMatrix, ExactPowerCoordinates.symmetricFormula_eq, map_mul]
      rfl

@[simp] theorem basis_apply (n m : ℕ) (i : Index n m) : basis flavor n m i =
    ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n
      (fieldBasis.exteriorPower n i.1) ⊗ₜ[ℂ] (Pi.basisFun ℂ (Fin 2)).symmetricPower m i.2 := by
  rcases i with ⟨i,j⟩
  simp [basis, transport, TensorProduct.congr, TensorProduct.map_tmul]
  rfl

theorem basis_repr_pure (n m : ℕ)
    (x : ⋀[ℂ]^n (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) 0))
    (y : Sym[ℂ]^m WeakDoubletScalars.Doublet) (i : Index n m) :
    (basis flavor n m).repr
      (ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n x ⊗ₜ[ℂ] y) i =
      (fieldBasis.exteriorPower n).repr x i.1 *
        ((Pi.basisFun ℂ (Fin 2)).symmetricPower m).repr y i.2 := by
  simp only [basis, Module.Basis.map_repr]
  change ((fieldBasis.exteriorPower n).tensorProduct
    ((Pi.basisFun ℂ (Fin 2)).symmetricPower m)).repr
      ((ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n).symm
        (ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n x) ⊗ₜ[ℂ] y) i = _
  rw [LinearEquiv.symm_apply_apply]
  simpa only [smul_eq_mul, mul_comm] using
    Module.Basis.tensorProduct_repr_tmul_apply (fieldBasis.exteriorPower n)
      ((Pi.basisFun ℂ (Fin 2)).symmetricPower m) x y i.1 i.2

def actionMatrix (n m : ℕ) (delta : ℤ) (d : SMGaussianLocalData.Data) :
    Matrix (Index n m) (Index n m) Scalar := fun i j =>
  ExactPowerCoordinates.exteriorMatrix n (fieldMatrix d) i.1 j.1 * bosonMatrix m delta d i.2 j.2

theorem action_sample_coordinate (n m : ℕ) (delta : ℤ) (t : SMRationalLocalKernel.Index n)
    (i j : Index n m) :
    (basis flavor n m).repr
      (SMIntegralLocalWeights.action flavor (pattern n) m delta (SMRationalLocalKernel.tests n t)
        (basis flavor n m j)) i = embed (actionMatrix n m delta (SMGaussianLocalData.data n t) i j) := by
  let g := SMRationalLocalKernel.tests n t
  let e := ConstantPatternExterior.linearEquiv (DeltaLOneSignedFields.field flavor) 0 n
  have hs := ConstantExteriorAction.forward_action (DeltaLOneSignedFields.field flavor) 0 n
    (g,1) (fieldBasis.exteriorPower n j.1)
  have hb := basis_apply flavor n m j
  have hinput : SMIntegralLocalWeights.action flavor (pattern n) m delta g (basis flavor n m j) =
      SMIntegralLocalWeights.source flavor (pattern n) g (e (fieldBasis.exteriorPower n j.1)) ⊗ₜ[ℂ]
        SMIntegralLocalWeights.boson (H := H) m delta g ((Pi.basisFun ℂ (Fin 2)).symmetricPower m j.2) :=
    congrArg (SMIntegralLocalWeights.action flavor (pattern n) m delta g) hb
  calc
    _ = (basis flavor n m).repr
        (SMIntegralLocalWeights.source flavor (pattern n) g (e (fieldBasis.exteriorPower n j.1)) ⊗ₜ[ℂ]
          SMIntegralLocalWeights.boson (H := H) m delta g
            ((Pi.basisFun ℂ (Fin 2)).symmetricPower m j.2)) i :=
      congrArg (fun x => (basis flavor n m).repr x i) hinput
    _ = (basis flavor n m).repr
        (e ((DeltaLOneSignedFields.field flavor 0).exteriorPower n (g,1)
          (fieldBasis.exteriorPower n j.1)) ⊗ₜ[ℂ]
          SMIntegralLocalWeights.boson (H := H) m delta g
            ((Pi.basisFun ℂ (Fin 2)).symmetricPower m j.2)) i :=
      congrArg (fun x => (basis flavor n m).repr
        (x ⊗ₜ[ℂ] SMIntegralLocalWeights.boson (H := H) m delta g
          ((Pi.basisFun ℂ (Fin 2)).symmetricPower m j.2)) i) hs
    _ = _ := by
      rw [basis_repr_pure]
      have hx := ExactPowerCoordinates.exterior_coordinate n fieldBasis
        (DeltaLOneSignedFields.field flavor 0 (g,1))
        (fieldMatrix (SMGaussianLocalData.data n t)) (field_sample_coordinate flavor n t) i.1 j.1
      have hy := boson_sample_coordinate (H := H) n m delta t i.2 j.2
      exact (congrArg₂ (fun x y : ℂ => x*y) hx hy).trans (map_mul embed _ _).symm

end
end GUT.SMQExactCoordinates
