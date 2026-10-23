import Math.RepresentationTheory.Tensors.TwoSlotYoung
import Math.RepresentationTheory.Exterior.ExteriorSquareTensorDescent

/-! Carrier-level comparison of two-slot Young components with the independent
symmetric and exterior square constructions. -/
namespace Math.TwoSlotYoungSquares
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H F : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ H F)

def symmetricProjection : IntertwiningMap (a.tprod a) (a.symmetricPower 2) where
  toLinearMap := TensorSquareMultilinear.fromMultilinear (SymmetricPower.tprod ℂ)
  isIntertwining' g := by
    ext u v
    change SymmetricPower.tprod ℂ ![a g u, a g v] =
      (a.symmetricPower 2) g (SymmetricPower.tprod ℂ ![u,v])
    convert (Representation.symmetricPower_apply_tprod a 2 g ![u,v]).symm using 1
    congr 1
    ext i
    fin_cases i <;> rfl

@[simp] theorem symmetricProjection_tmul (u v : F) :
    symmetricProjection a (u ⊗ₜ[ℂ] v) = SymmetricPower.tprod ℂ ![u,v] := rfl

theorem symmetricProjection_swap (u v : F) :
    symmetricProjection a (v ⊗ₜ[ℂ] u) = symmetricProjection a (u ⊗ₜ[ℂ] v) := by
  exact (TensorSquareMultilinear.symmetricSquareEquiv a (a.symmetricPower 2)).symm
    (IntertwiningMap.id _) |>.property u v

def symmetricProject : TensorSquareMultilinear.symmetricIntertwiners a (TwoSlotYoung.symmetric a) :=
    ⟨InvolutionYoung.project (a.tprod a) (TwoSlotYoung.swap a)
      (TwoSlotYoung.swap_involutive a) 1 (by norm_num), by
      intro u v
      apply Subtype.ext
      change InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1
        (v ⊗ₜ[ℂ] u) = InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1
        (u ⊗ₜ[ℂ] v)
      rw [TwoSlotYoung.symmetric_projector, TwoSlotYoung.symmetric_projector, add_comm]⟩

def symmetricEmbedding : IntertwiningMap (a.symmetricPower 2) (TwoSlotYoung.symmetric a) :=
  TensorSquareMultilinear.symmetricSquareEquiv a (TwoSlotYoung.symmetric a) (symmetricProject a)

@[simp] theorem symmetricEmbedding_tprod (v : Fin 2 → F) :
    (symmetricEmbedding a (SymmetricPower.tprod ℂ v)).val =
      InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1
        (v 0 ⊗ₜ[ℂ] v 1) := by
  let f := TensorSquareMultilinear.toEquivariant a (TwoSlotYoung.symmetric a) (symmetricProject a)
  change (SymmetricSquareDescent.lift f.val.val f.val.property (SymmetricPower.tprod ℂ v)).val = _
  rw [SymmetricSquareDescent.lift_tprod]
  rfl

theorem symmetric_projection_projector (w : F ⊗[ℂ] F) :
    symmetricProjection a (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1 w) =
      symmetricProjection a w := by
  have h : (symmetricProjection a).toLinearMap.comp
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1).toLinearMap =
      (symmetricProjection a).toLinearMap := by
    ext u v
    change symmetricProjection a
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1 (u ⊗ₜ[ℂ] v)) =
        symmetricProjection a (u ⊗ₜ[ℂ] v)
    rw [TwoSlotYoung.symmetric_projector, map_smul, map_add,
      symmetricProjection_swap]
    module
  exact congrArg (fun f : (F ⊗[ℂ] F) →ₗ[ℂ] Sym[ℂ]^2 F => f w) h

theorem symmetric_embedding_projection (w : F ⊗[ℂ] F) :
    (symmetricEmbedding a (symmetricProjection a w)).val =
      InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1 w := by
  have he : (Submodule.subtype (InvolutionYoung.eigen (a.tprod a) (TwoSlotYoung.swap a) 1)).comp
      ((symmetricEmbedding a).toLinearMap.comp (symmetricProjection a).toLinearMap) =
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1).toLinearMap := by
    ext u v
    change (symmetricEmbedding a (SymmetricPower.tprod ℂ ![u,v])).val = _
    exact symmetricEmbedding_tprod a ![u,v]
  exact congrArg (fun f : (F ⊗[ℂ] F) →ₗ[ℂ] (F ⊗[ℂ] F) => f w) he

def symmetricEquiv : Representation.Equiv (a.symmetricPower 2) (TwoSlotYoung.symmetric a) where
  toLinearEquiv :=
    { toLinearMap := (symmetricEmbedding a).toLinearMap
      invFun := fun w => symmetricProjection a w.val
      left_inv := by
        intro w
        have he : (symmetricProjection a).toLinearMap.comp
            ((InvolutionYoung.eigen (a.tprod a) (TwoSlotYoung.swap a) 1).subtype.comp
              (symmetricEmbedding a).toLinearMap) = LinearMap.id := by
          apply SymmetricSquareDescent.ext
          intro v
          change symmetricProjection a (symmetricEmbedding a (SymmetricPower.tprod ℂ v)).val = _
          rw [symmetricEmbedding_tprod, symmetric_projection_projector, symmetricProjection_tmul]
          have hv : ![v 0, v 1] = v := by
            ext i
            fin_cases i <;> rfl
          rw [hv]
          rfl
        exact congrArg (fun f : Sym[ℂ]^2 F →ₗ[ℂ] Sym[ℂ]^2 F => f w) he
      right_inv := by
        intro w
        apply Subtype.ext
        change (symmetricEmbedding a (symmetricProjection a w.val)).val = w.val
        rw [symmetric_embedding_projection]
        exact InvolutionYoung.projector_fixed (a.tprod a) (TwoSlotYoung.swap a) 1
          (by norm_num) w.val w.property }
  isIntertwining' := (symmetricEmbedding a).isIntertwining'

def exteriorProjection : IntertwiningMap (a.tprod a) (a.exteriorPower 2) where
  toLinearMap := ExteriorSquareTensorDescent.wedge
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u v
    change exteriorPower.ιMulti ℂ 2 ![a g u, a g v] =
      (a.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 ![u,v])
    rw [Representation.exteriorPower_apply_ιMulti]
    congr 1
    ext i
    fin_cases i <;> rfl

def exteriorProject : ExteriorSquareTensorDescent.antisymmetric
    (A := F) (N := InvolutionYoung.eigen (a.tprod a) (TwoSlotYoung.swap a) (-1)) :=
  ⟨(InvolutionYoung.project (a.tprod a) (TwoSlotYoung.swap a)
      (TwoSlotYoung.swap_involutive a) (-1) (by norm_num)).toLinearMap, by
    intro u v
    apply Subtype.ext
    change InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) (v ⊗ₜ[ℂ] u) =
      -InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) (u ⊗ₜ[ℂ] v)
    rw [TwoSlotYoung.antisymmetric_projector, TwoSlotYoung.antisymmetric_projector]
    module⟩

def exteriorEmbedding : IntertwiningMap (a.exteriorPower 2) (TwoSlotYoung.antisymmetric a) where
  toLinearMap := ExteriorSquareTensorDescent.equiv (exteriorProject a)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply]
    change ExteriorSquareTensorDescent.equiv (exteriorProject a)
        ((a.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v)) =
      (TwoSlotYoung.antisymmetric a) g
        (ExteriorSquareTensorDescent.equiv (exteriorProject a) (exteriorPower.ιMulti ℂ 2 v))
    rw [Representation.exteriorPower_apply_ιMulti,
      ExteriorSquareTensorDescent.equiv_apply, ExteriorSquareTensorDescent.equiv_apply]
    exact IntertwiningMap.isIntertwining _ _
      (InvolutionYoung.project (a.tprod a) (TwoSlotYoung.swap a)
        (TwoSlotYoung.swap_involutive a) (-1) (by norm_num)) g (v 0 ⊗ₜ[ℂ] v 1)

@[simp] theorem exteriorEmbedding_wedge (v : Fin 2 → F) :
    (exteriorEmbedding a (exteriorPower.ιMulti ℂ 2 v)).val =
      InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1)
        (v 0 ⊗ₜ[ℂ] v 1) := by
  change (ExteriorSquareTensorDescent.equiv (exteriorProject a) (exteriorPower.ιMulti ℂ 2 v)).val = _
  rw [ExteriorSquareTensorDescent.equiv_apply]
  rfl

theorem exterior_projection_projector (w : F ⊗[ℂ] F) :
    exteriorProjection a (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) w) =
      exteriorProjection a w := by
  have he : (exteriorProjection a).toLinearMap.comp
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1)).toLinearMap =
        (exteriorProjection a).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change ExteriorSquareTensorDescent.wedge
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) (u ⊗ₜ[ℂ] v)) =
      ExteriorSquareTensorDescent.wedge (u ⊗ₜ[ℂ] v)
    rw [TwoSlotYoung.antisymmetric_projector, map_smul, map_sub,
      ExteriorSquareTensorDescent.wedge_swap]
    module
  exact congrArg (fun f : (F ⊗[ℂ] F) →ₗ[ℂ] ⋀[ℂ]^2 F => f w) he

theorem exterior_embedding_projection (w : F ⊗[ℂ] F) :
    (exteriorEmbedding a (exteriorProjection a w)).val =
      InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) w := by
  have he : (InvolutionYoung.eigen (a.tprod a) (TwoSlotYoung.swap a) (-1)).subtype.comp
      ((exteriorEmbedding a).toLinearMap.comp (exteriorProjection a).toLinearMap) =
        (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1)).toLinearMap := by
    ext u v
    exact exteriorEmbedding_wedge a ![u,v]
  exact congrArg (fun f : (F ⊗[ℂ] F) →ₗ[ℂ] (F ⊗[ℂ] F) => f w) he

def exteriorEquiv : Representation.Equiv (a.exteriorPower 2) (TwoSlotYoung.antisymmetric a) where
  toLinearEquiv :=
    { toLinearMap := (exteriorEmbedding a).toLinearMap
      invFun := fun w => exteriorProjection a w.val
      left_inv := by
        intro w
        have he : (exteriorProjection a).toLinearMap.comp
            ((InvolutionYoung.eigen (a.tprod a) (TwoSlotYoung.swap a) (-1)).subtype.comp
              (exteriorEmbedding a).toLinearMap) = LinearMap.id := by
          apply exteriorPower.linearMap_ext
          apply AlternatingMap.ext
          intro v
          change exteriorProjection a (exteriorEmbedding a (exteriorPower.ιMulti ℂ 2 v)).val = _
          rw [exteriorEmbedding_wedge, exterior_projection_projector]
          change exteriorPower.ιMulti ℂ 2 ![v 0,v 1] = exteriorPower.ιMulti ℂ 2 v
          have hv : ![v 0,v 1] = v := by ext i; fin_cases i <;> rfl
          rw [hv]
        exact congrArg (fun f : (⋀[ℂ]^2 F) →ₗ[ℂ] ⋀[ℂ]^2 F => f w) he
      right_inv := by
        intro w
        apply Subtype.ext
        change (exteriorEmbedding a (exteriorProjection a w.val)).val = w.val
        rw [exterior_embedding_projection]
        exact InvolutionYoung.projector_fixed (a.tprod a) (TwoSlotYoung.swap a) (-1)
          (by norm_num) w.val w.property }
  isIntertwining' := (exteriorEmbedding a).isIntertwining'

def componentsEquiv : Representation.Equiv
    ((a.symmetricPower 2).prod (a.exteriorPower 2))
    ((TwoSlotYoung.symmetric a).prod (TwoSlotYoung.antisymmetric a)) where
  toLinearEquiv := (symmetricEquiv a).toLinearEquiv.prodCongr (exteriorEquiv a).toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply Prod.ext
    · exact IntertwiningMap.isIntertwining _ _ (symmetricEmbedding a) g w.1
    · exact IntertwiningMap.isIntertwining _ _ (exteriorEmbedding a) g w.2

/-- Tensor square splits into the independently defined symmetric/exterior
squares, with explicit projectors and no finite-dimensionality hypothesis. -/
def splitting : Representation.Equiv (a.tprod a)
    ((a.symmetricPower 2).prod (a.exteriorPower 2)) :=
  (TwoSlotYoung.splitting a).trans (componentsEquiv a).symm

@[simp] theorem splitting_tmul (u v : F) :
    splitting a (u ⊗ₜ[ℂ] v) =
      (SymmetricPower.tprod ℂ ![u,v], exteriorPower.ιMulti ℂ 2 ![u,v]) := by
  apply Prod.ext
  · change symmetricProjection a
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) 1 (u ⊗ₜ[ℂ] v)) = _
    rw [symmetric_projection_projector, symmetricProjection_tmul]
  · change exteriorProjection a
      (InvolutionYoung.projector (a.tprod a) (TwoSlotYoung.swap a) (-1) (u ⊗ₜ[ℂ] v)) = _
    rw [exterior_projection_projector]
    rfl

@[simp] theorem splitting_symm_symmetric (u v : F) :
    (splitting a).symm (SymmetricPower.tprod ℂ ![u,v], 0) =
      (1 / 2 : ℂ) • (u ⊗ₜ[ℂ] v + v ⊗ₜ[ℂ] u) := by
  change (symmetricEmbedding a (SymmetricPower.tprod ℂ ![u,v])).val +
    (exteriorEmbedding a 0).val = _
  rw [map_zero]
  simp only [ZeroMemClass.coe_zero, add_zero]
  rw [symmetricEmbedding_tprod]
  exact TwoSlotYoung.symmetric_projector a u v

@[simp] theorem splitting_symm_exterior (u v : F) :
    (splitting a).symm (0, exteriorPower.ιMulti ℂ 2 ![u,v]) =
      (1 / 2 : ℂ) • (u ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] u) := by
  change (symmetricEmbedding a 0).val +
    (exteriorEmbedding a (exteriorPower.ιMulti ℂ 2 ![u,v])).val = _
  rw [map_zero]
  simp only [ZeroMemClass.coe_zero, zero_add]
  rw [exteriorEmbedding_wedge]
  exact TwoSlotYoung.antisymmetric_projector a u v

def symmetricQuotientEquiv :=
  (TwoSlotYoung.symmetricQuotientEquiv a).trans (symmetricEquiv a).symm

def exteriorQuotientEquiv :=
  (TwoSlotYoung.antisymmetricQuotientEquiv a).trans (exteriorEquiv a).symm

end
end Math.TwoSlotYoungSquares
