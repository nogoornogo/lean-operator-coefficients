import Physics.StandardModel.Operators.Support.Coordinates.SMWeakWeightBasis
import Math.RepresentationTheory.Exterior.PatternExteriorSource

/-! Content-specific weak bound on the actual exterior-statistical source. -/
namespace Physics.SMContentWeakBound
set_option autoImplicit false
noncomputable section
open Math Representation BoundedTorusWeights SMWeakWeightBasis
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

@[reducible] local instance : AddCommGroup
    (⨂[ℂ] i : Fin n, DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) (p i)) :=
  inferInstance

def bound : ℕ := ∑ i, doubletCount (p i)
abbrev source := PatternExteriorSource.representation (DeltaLOneSignedFields.field flavor) p

def tensorBasis : Module.Basis (∀ i, FieldIndex (p i)) ℂ
    (⨂[ℂ] i : Fin n, DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) (p i)) :=
  Basis.piTensorProduct (fun i => fieldBasis (p i))
def tensorWeight (j : ∀ i, FieldIndex (p i)) : ℤ := ∑ i, gaugeWeight (p i) (j i).1.1

theorem tensor_basis_eigen (j : ∀ i, FieldIndex (p i)) :
    Eigen (PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) p)
      (fullTorus (H := H)) (tensorWeight p j) (tensorBasis p j) := by
  intro z
  rw [tensorBasis, Basis.piTensorProduct_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod]
  have hb (i : Fin n) := field_basis_eigen flavor (p i) (j i) z
  simp_rw [hb]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  rw [ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero]
  rfl

theorem tensor_weight_bound (j : ∀ i, FieldIndex (p i)) :
    -(bound p : ℤ) ≤ tensorWeight p j ∧ tensorWeight p j ≤ bound p := by
  simp only [bound, tensorWeight, Nat.cast_sum]
  constructor
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => (gauge_weight_bound (p i) (j i).1.1).1)
  · exact Finset.sum_le_sum (fun i _ => (gauge_weight_bound (p i) (j i).1.1).2)

theorem raw_bounded :
    Bounded (PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) p)
      (fullTorus (H := H)) (bound p) :=
  of_basis _ _ (tensorBasis p) (tensorWeight p) (bound p)
    (tensor_basis_eigen flavor p) (tensor_weight_bound p)

theorem source_bounded : Bounded (source flavor p) (fullTorus (H := H)) (bound p) :=
  bounded_of_surjective (PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) p)
    (fullTorus (H := H)) (source flavor p)
    (PatternExteriorSource.onto (DeltaLOneSignedFields.field flavor) p)
    (PatternExteriorSource.onto_surjective (DeltaLOneSignedFields.field flavor) p)
    _ (raw_bounded flavor p)

theorem source_dual_eigen_zero (w : ℤ)
    (hw : (bound p : ℤ) < w ∨ w < -(bound p : ℤ))
    (f : Module.Dual ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p))
    (hf : Eigen (source flavor p).dual (fullTorus (H := H)) w f) : f=0 :=
  dual_eigen_zero (source flavor p) (fullTorus (H := H)) (bound p)
    (source_bounded flavor p) w hw f hf

theorem bound_le_degree : bound p ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => by
      simp only [doubletCount]; split_ifs <;> omega)
    _ = n := by simp

def pilot : Fin 2 → DeltaLOneSignedInput.Species := fun _ => 0
theorem pilot_bound : bound pilot = 2 := by decide

def hypercharge : ℤ := ∑ i, DeltaLOneSignedInput.hypercharge (p i)

theorem raw_hypercharge (z : Circle) :
    (PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) p)
      (DeltaLOneSignedFields.fullHypercharge z) =
    (z : ℂ)^hypercharge p • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  simp_rw [DeltaLOneSignedFields.field_hypercharge flavor z]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ,
    ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero]
  rfl

theorem source_hypercharge (z : Circle) (x : PatternExteriorSource.Source
    (DeltaLOneSignedFields.field flavor) p) :
    source flavor p (DeltaLOneSignedFields.fullHypercharge z) x =
      (z : ℂ)^hypercharge p • x :=
  PatternExteriorSource.source_scalar (DeltaLOneSignedFields.field flavor) p
    (DeltaLOneSignedFields.fullHypercharge z) _ (raw_hypercharge flavor p z) x

end
end Physics.SMContentWeakBound
