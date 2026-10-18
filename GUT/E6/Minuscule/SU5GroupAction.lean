import GUT.E6.Minuscule.SU5ModelComparison
import Math.RepresentationTheory.Decomposition.RepresentationConjugation

open Math

/-! The actual SU(5) action on the minuscule coordinates, before proving
membership in the compact E6 candidate. -/

set_option autoImplicit false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open GUT.SU5
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

abbrev SU5 := StandardModelEmbedding.TargetGroup

def dualPairRepresentation : Representation ℂ SU5 (Fin 2 → Matter.BarFive) where
  toFun g := LinearMap.pi fun k => (Matter.antifundamental g).comp (LinearMap.proj k)
  map_one' := by ext v k; simp
  map_mul' g h := by ext v k; simp

def modelRepresentation : Representation ℂ SU5 Model :=
  (1 : Representation ℂ SU5 (Fin 2 → ℂ)).prod
    (Matter.fundamental.prod (dualPairRepresentation.prod Matter.ten))

def coordinateRepresentation : Representation ℂ SU5 (Index → ℂ) :=
  RepresentationConjugation.pullback modelCoordinates.symm modelRepresentation

def coordinateAction : SU5 →* Matrix Index Index ℂ :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp coordinateRepresentation

/-- Change of matrices in the fixed signed orthonormal coordinates. -/
def matrixCoordinates : Matrix27 ≃ₐ[ℂ] Matrix Index Index ℂ :=
  Matrix.toLinAlgEquiv'.trans
    ((signedCoordinates.conjAlgEquiv ℂ).trans LinearMap.toMatrixAlgEquiv')

def groupAction : SU5 →* Matrix27 :=
  matrixCoordinates.symm.toMonoidHom.comp coordinateAction

theorem matrixCoordinates_mulVec (M : Matrix27) (v : Fin 27 → ℂ) :
    matrixCoordinates M *ᵥ signedCoordinates v = signedCoordinates (M *ᵥ v) := by
  change (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv'
    (signedCoordinates.conjAlgEquiv ℂ (Matrix.toLinAlgEquiv' M)))) (signedCoordinates v) = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  change signedCoordinates (M *ᵥ signedCoordinates.symm (signedCoordinates v)) = _
  rw [signedCoordinates.symm_apply_apply]

theorem signedCoordinates_symm_single (b : Index) :
    signedCoordinates.symm (Pi.single b 1) =
      (sign b : ℂ) • Pi.single (coordinateEquiv b) 1 := by
  apply signedCoordinates.injective
  rw [signedCoordinates.apply_symm_apply]
  funext a
  change (Pi.single b 1 : Index → ℂ) a = (sign a : ℂ) *
    ((sign b : ℂ) * (Pi.single (coordinateEquiv b) 1 : Fin 27 → ℂ) (coordinateEquiv a))
  by_cases h : a = b
  · subst a
    simp [sign_sq_complex]
  · have hc := coordinate_bijective.injective.ne h
    simp [h, hc]

theorem matrixCoordinates_apply (M : Matrix27) (a b : Index) :
    matrixCoordinates M a b =
      (sign a : ℂ) * M (coordinate a) (coordinate b) * (sign b : ℂ) := by
  have h := congrFun (matrixCoordinates_mulVec M (signedCoordinates.symm (Pi.single b 1))) a
  rw [signedCoordinates.apply_symm_apply, signedCoordinates_symm_single] at h
  simpa [Matrix.mulVec_smul, Matrix.mulVec_single, signedCoordinates, mul_comm,
    mul_left_comm, mul_assoc] using h

theorem matrixCoordinates_adjoint (M : Matrix27) :
    matrixCoordinates Mᴴ = (matrixCoordinates M)ᴴ := by
  ext a b
  simp only [matrixCoordinates_apply, Matrix.conjTranspose_apply, star_mul, star_intCast]
  ring

def actionBlock (g : SU5) : Matrix Index Index ℂ
  | .inl a, .inl b => if a = b then 1 else 0
  | .inr (.inl a), .inr (.inl b) => g.val a b
  | .inr (.inr (.inl (k, a))), .inr (.inr (.inl (l, b))) =>
      if k = l then (g⁻¹).val b a else 0
  | .inr (.inr (.inr a)), .inr (.inr (.inr b)) => exteriorMatrix g.val a b
  | _, _ => 0

theorem modelRepresentation_coordinates (g : SU5) (v : Model) :
    modelCoordinates (modelRepresentation g v) = actionBlock g *ᵥ modelCoordinates v := by
  funext a
  rcases a with a | a | ⟨k, a⟩ | a
  · simp [modelCoordinates, modelRepresentation, Matrix.mulVec, dotProduct, actionBlock,
      Fintype.sum_sum_type]
  · simp [modelCoordinates, modelRepresentation, Matter.fundamental, Matrix.mulVec,
      dotProduct, actionBlock, Fintype.sum_sum_type, Matrix.toLin'_apply]
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr UnitaryMatter.barFiveBasis
      UnitaryMatter.barFiveBasis (Matter.antifundamental g) (v.2.2.1 k)) a
    rw [matter_barFive_matrix] at h
    simpa [modelCoordinates, modelRepresentation, dualPairRepresentation, Matrix.mulVec,
      dotProduct, actionBlock, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Module.Basis.equivFun_apply] using h.symm
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr exteriorBasis exteriorBasis
      (Matter.ten g) v.2.2.2) a
    rw [matter_ten_matrix] at h
    simpa [modelCoordinates, modelRepresentation, Matrix.mulVec, dotProduct, actionBlock,
      Fintype.sum_sum_type, Module.Basis.equivFun_apply] using h.symm

theorem coordinateAction_eq (g : SU5) : coordinateAction g = actionBlock g := by
  apply Matrix.toLinAlgEquiv'.injective
  apply LinearMap.ext
  intro v
  funext a
  change (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (coordinateRepresentation g))) v a = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  change (coordinateRepresentation g v) a = (actionBlock g *ᵥ v) a
  have h := congrFun (modelRepresentation_coordinates g (modelCoordinates.symm v)) a
  simpa [coordinateRepresentation, RepresentationConjugation.pullback] using h

theorem coordinateAction_continuous : Continuous coordinateAction := by
  have hg (i j : Fin 5) : Continuous (fun g : SU5 => g.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  apply continuous_matrix
  intro a b
  simp_rw [coordinateAction_eq]
  rcases a with a | a | ⟨k, a⟩ | a <;> rcases b with b | b | ⟨l, b⟩ | b
  all_goals dsimp only [actionBlock]
  all_goals try exact continuous_const
  · exact hg a b
  · split_ifs
    · exact (hg b a).comp continuous_inv
    · exact continuous_const
  · simp_rw [exteriorMatrix_minor]
    exact ((hg _ _).mul (hg _ _)).sub ((hg _ _).mul (hg _ _))

theorem coordinateAction_injective : Function.Injective coordinateAction := by
  intro g h he
  apply Subtype.ext
  ext a b
  have := congrArg (fun M : Matrix Index Index ℂ => M (.inr (.inl a)) (.inr (.inl b))) he
  simpa [coordinateAction_eq, actionBlock] using this

theorem groupAction_continuous : Continuous groupAction :=
  matrixCoordinates.symm.toLinearMap.continuous_of_finiteDimensional.comp
    coordinateAction_continuous

theorem groupAction_injective : Function.Injective groupAction :=
  matrixCoordinates.symm.injective.comp coordinateAction_injective

end

end GUT.E6.Minuscule.SU5Coordinates
