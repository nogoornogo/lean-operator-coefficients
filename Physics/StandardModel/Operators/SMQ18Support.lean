import Physics.StandardModel.Operators.SMGenerationSupport
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Math.RepresentationTheory.SelfDualCoefficient

/-! Structural Q18 support from the perfect middle exterior pairing.
No character recurrence, numerical multiplicity or rank certificate is used. -/
namespace GUT.SMQ18Support
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy
open scoped TensorProduct

attribute [local irreducible] TopExteriorCauchy.map SymmetricCauchy.map
  SU2SymmetricEmbeddings.omegaPower

abbrev Field := ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
  WeakDoubletScalars.Doublet) ⊗[ℂ] (Fin 3 → ℂ)

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
      WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup Field := inferInstance

abbrev rho : Representation ℂ Group Field := generations SMGenerationCauchy.quark

theorem field_dimension : Module.finrank ℂ Field = 36 := by
  simp [Field, SMEpsilonTensor.Color, WeakDoubletScalars.Doublet,
    Module.finrank_tensorProduct]

theorem weak_det (g : Group) : LinearMap.det (weak g) = 1 := by
  change LinearMap.det (Matrix.toLin' (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [LinearMap.det_toLin']
  exact g.2.1.prop.2

theorem field_det (g : Group) : LinearMap.det (rho g) = 1 := by
  have hq : LinearMap.det (quark g) = 1 :=
    TensorDeterminant.map_one (colorBasis.tensorProduct spinBasis) spinBasis
      ((color.tprod weak) g) (spin g)
      (TensorDeterminant.map_one colorBasis spinBasis (color g) (weak g)
        (color_det g) (weak_det g)) (spin_det g)
  exact TensorDeterminant.map_one
    ((colorBasis.tensorProduct spinBasis).tensorProduct spinBasis)
    (Pi.basisFun ℂ (Fin 3)) (quark g) (LinearMap.id) hq (by simp)

def middleDuality : Representation.Equiv (rho.exteriorPower 18)
    (rho.exteriorPower 18).dual :=
  ComplementaryExteriorDuality.equiv rho field_det
    (exteriorPower.topEquiv (Module.finBasis ℂ Field)) (by rw [field_dimension])

theorem semisimple_allowed (m : ℕ) (hm : m % 2 = 0) (hmax : m ≤ 18) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((rho.exteriorPower 18).tprod (weak.symmetricPower m))) := by
  let : Nontrivial (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      change 0 < Module.finrank ℂ (Sym[ℂ]^m (Fin 2 → ℂ))
      rw [TauCeti.SU2.finrank_symPower]
      omega)
  obtain ⟨f,hf⟩ := SMGenerationSupport.quark_eighteen m hm hmax
  exact SelfDualCoefficient.allowed _ _ middleDuality f hf

end
end GUT.SMQ18Support
