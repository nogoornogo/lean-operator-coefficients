import Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.Support.Coordinates.SMChiralitySupport
import Math.RepresentationTheory.Weights.SubrepresentationTorusBound

/-! Independent left/right spin bounds for the actual statistical source.
The side bound counts only that chirality's slots; gauge and flavor bases
remain symbolic and do not contribute to these weights. -/
namespace Physics.SMCompactSpinBound
set_option autoImplicit false
noncomputable section
open Math Representation BoundedTorusWeights SMWeakWeightBasis
open scoped TensorProduct

def spinTorus (side : Bool) : Circle →* SMCombinedCompactAction.Spin :=
  (if side then MonoidHom.inr _ _ else MonoidHom.inl _ _).comp TauCeti.SU2.torusHom
def torus (side : Bool) : Circle →* SMCombinedCompactAction.Group :=
  (MonoidHom.inr _ _).comp (spinTorus side)
def weight (side b : Bool) (i : Fin 2) : ℤ := if b=side then weakWeight i else 0

theorem spin_eigen (side b : Bool) (i : Fin 2) (z : Circle) :
    WeylIndependentAction.spin b (SMMixedCompactWeyl.compact (spinTorus side z))
      (Pi.basisFun ℂ (Fin 2) i) = (z : ℂ)^weight side b i • Pi.basisFun ℂ (Fin 2) i := by
  cases side <;> cases b
  · change StandardSMGaugeTensor.weak (gaugeTorus z) (Pi.basisFun ℂ (Fin 2) i) =
      (z : ℂ)^weakWeight i • Pi.basisFun ℂ (Fin 2) i
    exact weak_basis_eigen i z
  · simp [spinTorus,weight,WeylIndependentAction.spin,SMMixedCompactWeyl.compact]
  · simp [spinTorus,weight,WeylIndependentAction.spin,SMMixedCompactWeyl.compact]
  · change StandardSMGaugeTensor.weak (gaugeTorus z) (Pi.basisFun ℂ (Fin 2) i) =
      (z : ℂ)^weakWeight i • Pi.basisFun ℂ (Fin 2) i
    exact weak_basis_eigen i z

def fieldWeight (side : Bool) (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) : ℤ :=
  weight side (DeltaLOneSignedFields.rightHanded s) i.1.2

theorem field_eigen (side : Bool) (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) :
    Eigen (SMCombinedCompactAction.field s) (torus side) (fieldWeight side s i) (fieldBasis s i) := by
  rcases i with ⟨⟨a,b⟩,c⟩
  intro z
  simp only [fieldBasis,Module.Basis.tensorProduct_apply]
  change (DeltaLOneSignedFields.gauge s 1 (gaugeBasis s a) ⊗ₜ[ℂ]
    WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)
      (SMMixedCompactWeyl.compact (spinTorus side z)) (Pi.basisFun ℂ (Fin 2) b)) ⊗ₜ[ℂ]
      Pi.basisFun ℂ (Fin 3) c = _
  rw [map_one]
  simp only [Module.End.one_apply]
  rw [spin_eigen]
  simp only [TensorProduct.tmul_smul,fieldWeight,TensorProduct.smul_tmul']

theorem field_bound (side : Bool) (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) :
    -(SMChiralitySupport.slotCount side s : ℤ) ≤ fieldWeight side s i ∧
      fieldWeight side s i ≤ SMChiralitySupport.slotCount side s := by
  unfold fieldWeight weight SMChiralitySupport.slotCount weakWeight
  split_ifs <;> omega

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def tensorWeight (side : Bool) (i : ∀ j, FieldIndex (p j)) : ℤ := ∑ j, fieldWeight side (p j) (i j)

theorem raw_bounded (side : Bool) :
    Bounded (PatternExteriorSource.Raw SMCombinedCompactAction.field p) (torus side)
      (SMChiralitySupport.count p side) := by
  apply of_basis _ _ (SMContentWeakBound.tensorBasis p) (tensorWeight p side)
  · intro i z
    rw [SMContentWeakBound.tensorBasis,Basis.piTensorProduct_apply,
      MultilinearInvariantHom.tensorRepresentation_tprod]
    have he (j : Fin n) := field_eigen side (p j) (i j) z
    simp_rw [he]
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ,ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero]
    rfl
  · intro i
    simp only [tensorWeight,SMChiralitySupport.count,Nat.cast_sum]
    constructor
    · rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun j _ => (field_bound side (p j) (i j)).1)
    · exact Finset.sum_le_sum (fun j _ => (field_bound side (p j) (i j)).2)

theorem source_bounded (side : Bool) :
    Bounded (SMCombinedCompactAction.source flavor p) (torus side) (SMChiralitySupport.count p side) :=
  bounded_of_surjective _ _ _ (PatternExteriorSource.onto SMCombinedCompactAction.field p)
    (PatternExteriorSource.onto_surjective SMCombinedCompactAction.field p) _ (raw_bounded p side)

theorem model_bounded (side : Bool) :
    Bounded (SMCombinedCompactContinuity.sourceModel flavor p) (torus side)
      (SMChiralitySupport.count p side) :=
  SubrepresentationTorusBound.alongEquiv
    (ContinuousUnitaryConstructions.basisCopyRepresentationEquiv
      (SMCombinedCompactContinuity.sourceBasis flavor p) (SMCombinedCompactAction.source flavor p))
    (torus side) _ (source_bounded flavor p side)

end
end Physics.SMCompactSpinBound
