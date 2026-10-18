import Math.RepresentationTheory.Decomposition.FirstSummandEmbedding
import GUT.SU6.SelectionRules.Models.StandardSMUVFields
import GUT.SU6.SelectionRules.Models.StandardSMUVCoordinates

/-! Action of a supplied diagonal scalar-block SU(6) element on the
actual standard branching. No homomorphic lift is assumed. -/
namespace GUT.StandardScalarBlock
set_option autoImplicit false
noncomputable section
open Math StandardSMExterior StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

def coords (c w t : ℂ) : Fin 6 → ℂ := ![c,c,c,w,w,t]

def six (c w t : ℂ) (x : Six) : Six := (c • x.1, (w • x.2.1, t * x.2.2))

def blocks (c w t : ℂ) (x : Blocks) : Blocks :=
  ((c*c) • x.1, ((c*w) • x.2.1, ((w*w) • x.2.2.1,
    ((c*t) • x.2.2.2.1, (w*t) • x.2.2.2.2))))

theorem fundamental_action (s : ActualRestriction.SU6) (c w t : ℂ)
    (hs : (s : Matrix (Fin 6) (Fin 6) ℂ) = Matrix.diagonal (coords c w t))
    (v : Fin 6 → ℂ) :
    StandardSMGroup.splitEquiv (FundamentalRepresentation.rho s v) =
      six c w t (StandardSMGroup.splitEquiv v) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [StandardSMGroup.splitEquiv, FundamentalRepresentation.rho,
      Matrix.toLin'_apply, hs, six, coords, Matrix.mulVec_diagonal]
  · apply Prod.ext
    · funext i
      fin_cases i <;> simp [StandardSMGroup.splitEquiv, FundamentalRepresentation.rho,
        Matrix.toLin'_apply, hs, six, coords, Matrix.mulVec_diagonal]
    · simp [StandardSMGroup.splitEquiv, FundamentalRepresentation.rho,
        Matrix.toLin'_apply, hs, six, coords, Matrix.mulVec_diagonal]

theorem pair_action (c w t : ℂ) (x y : Six) :
    pair (six c w t x) (six c w t y) = blocks c w t (pair x y) := by
  simp [pair, six, blocks, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc, eps2, mul_sub]

def blocksLinear (c w t : ℂ) : Blocks →ₗ[ℂ] Blocks where
  toFun := blocks c w t
  map_add' x y := by simp [blocks, smul_add]
  map_smul' z x := by simp [blocks, smul_smul, mul_comm]

theorem branch_action (s : ActualRestriction.SU6) (c w t : ℂ)
    (hs : (s : Matrix (Fin 6) (Fin 6) ℂ) = Matrix.diagonal (coords c w t))
    (v : ⋀[ℂ]^2 (Fin 6 → ℂ)) :
    branch (exteriorPower.map 2 (FundamentalRepresentation.rho s) v) =
      blocks c w t (branch v) := by
  have he : branch.comp (exteriorPower.map 2 (FundamentalRepresentation.rho s)) =
      (blocksLinear c w t).comp branch := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    change branch (exteriorPower.map 2 (FundamentalRepresentation.rho s)
      (exteriorPower.ιMulti ℂ 2 f)) = blocks c w t (branch (exteriorPower.ιMulti ℂ 2 f))
    rw [exteriorPower.map_apply_ιMulti, branch_wedge, branch_wedge]
    change pair (StandardSMGroup.splitEquiv (FundamentalRepresentation.rho s (f 0)))
      (StandardSMGroup.splitEquiv (FundamentalRepresentation.rho s (f 1))) =
      blocks c w t (pair (StandardSMGroup.splitEquiv (f 0)) (StandardSMGroup.splitEquiv (f 1)))
    rw [fundamental_action s c w t hs, fundamental_action s c w t hs]
    exact pair_action c w t _ _
  exact LinearMap.congr_fun he v

set_option backward.isDefEq.respectTransparency false in
theorem analytic_action (s : ActualRestriction.SU6) (c w t : ℂ)
    (hs : (s : Matrix (Fin 6) (Fin 6) ℂ) = Matrix.diagonal (coords c w t))
    (v : ConcreteSU6Representations.exteriorTwo.V) :
    StandardSMExterior.analyticEquiv (ConcreteSU6Representations.exteriorTwo.rho s v) =
      blocks c w t (StandardSMExterior.analyticEquiv v) := by
  change branch (ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm
    (ConcreteSU6Representations.exteriorTwo.rho s v)) =
    blocks c w t (branch (ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm v))
  have he := Representation.IntertwiningMap.isIntertwining _ _
    ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm.toIntertwiningMap s v
  have hb := congrArg branch he
  change branch (ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm
    (ConcreteSU6Representations.exteriorTwo.rho s v)) =
    branch (exteriorPower.map 2 (FundamentalRepresentation.rho s)
      (ConcreteSU6Representations.exteriorTwoAlgebraicEquiv.symm v)) at hb
  exact hb.trans (branch_action s c w t hs _)

def embedding (x : Blocks) : StandardSMUVFields.UV :=
  FirstSummandEmbedding.embedding StandardSMExterior.analyticEquiv.toLinearEquiv x

theorem embedding_add (x y : Blocks) : embedding (x+y) = embedding x + embedding y :=
  (FirstSummandEmbedding.linear StandardSMExterior.analyticEquiv.toLinearEquiv).map_add x y

theorem embedding_smul (z : ℂ) (x : Blocks) : embedding (z • x) = z • embedding x :=
  (FirstSummandEmbedding.linear StandardSMExterior.analyticEquiv.toLinearEquiv).map_smul z x

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have he := congrArg (fun z : StandardSMUVFields.UV =>
    StandardSMExterior.analyticEquiv.toLinearEquiv z.1.1) h
  simpa only [embedding, FirstSummandEmbedding.embedding, LinearEquiv.apply_symm_apply] using he


set_option backward.isDefEq.respectTransparency false in
theorem embedding_decomposed (x : Blocks) :
    StandardSMUVFields.gaugeEquiv (embedding x) =
      ((StandardSMUVFields.reorder (x, 0)), 0) := by
  exact FirstSummandEmbedding.decomposed StandardSMExterior.analyticEquiv
    StandardSMContragredient.antifundamentalEquiv
    StandardSMGroup.analyticAntifundamentalEquiv StandardSMUVFields.reorderEquiv x

set_option backward.isDefEq.respectTransparency false in
theorem embedding_mem_radical (x : Blocks)
    (hc : x.2.2.2.1 = 0) (hw : x.2.2.2.2 = 0) :
    embedding x ∈ (StandardSMUVMass.mass Unit).radical.toSubmodule := by
  rw [StandardSMUVMass.mem_radical_iff, StandardSMUVFields.withResidualEquiv_apply]
  rw [embedding_decomposed]
  rw [StandardSMFullGaugeMass.mem_radical_iff]
  simp [StandardSMUVFields.reorder, hc, hw, StandardSMUVFields.singletEquiv]

end
end GUT.StandardScalarBlock
