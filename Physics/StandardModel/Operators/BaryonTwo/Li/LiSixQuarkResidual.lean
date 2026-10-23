import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorOneGeneration

open Math

/-! The extended local orbit coordinates on the existing typed residual Hom.
All four statistics equations are transported, not discarded. -/
namespace Physics.LiSixQuarkResidual
set_option autoImplicit false
set_option maxRecDepth 5000
noncomputable section
open Representation SixQuarkFlavorCoordinates SixQuarkFlavorResidualHom
open LiSixQuarkCertificate

universe u
variable {H : Type*} [Group H]
  (U D : Type u) [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  (up : Representation ℂ H U) (down : Representation ℂ H D)

abbrev slots := SixQuarkTypedFlavor.slotRepresentation U D up down
abbrev OrbitHom := IntertwiningMap (MultilinearInvariantHom.tensorRepresentation
  (slots U D up down)) (Representation.trivial ℂ H (Fin 25 → ℂ))

/-- At every flavor input, the transported coordinates assemble the literal
selected orbit contractions, rather than an unrelated abstract inverse. -/
theorem literal_local_assembly (k : OrbitHom U D up down)
    (t : ∀ i, SixQuarkTypedFlavor.SlotFlavor U D i) :
    SixQuarkInvariant.reconstruct (coordinateEquiv (k (PiTensorProduct.tprod ℂ t))) =
      ∑ j, k (PiTensorProduct.tprod ℂ t) j • LiSixQuarkLocalBasis.orbitCoefficient j := by
  have he := congrArg Subtype.val
    (LiSixQuarkLocalBasis.localEquiv_assembly (k (PiTensorProduct.tprod ℂ t)))
  simpa [LiSixQuarkLocalBasis.localEquiv, LiSixQuarkLocalBasis.orbitInvariant,
    SixQuarkPermutationCompleteness.coordinatesEquiv] using he

def extractHom (k : Hom (slots U D up down)) : OrbitHom U D up down where
  toLinearMap := coordinateEquiv.symm.toLinearMap.comp k.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change coordinateEquiv.symm (k ((MultilinearInvariantHom.tensorRepresentation
      (slots U D up down)) g x)) = coordinateEquiv.symm (k x)
    congr 1
    simpa using IntertwiningMap.isIntertwining _ _ k g x

def assembleHom (k : OrbitHom U D up down) : Hom (slots U D up down) where
  toLinearMap := coordinateEquiv.toLinearMap.comp k.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change coordinateEquiv (k ((MultilinearInvariantHom.tensorRepresentation
      (slots U D up down)) g x)) = coordinateEquiv (k x)
    congr 1
    simpa using IntertwiningMap.isIntertwining _ _ k g x

def homEquiv : Hom (slots U D up down) ≃ₗ[ℂ] OrbitHom U D up down where
  toFun := extractHom U D up down
  invFun := assembleHom U D up down
  left_inv k := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact coordinateEquiv.apply_symm_apply (k x)
  right_inv k := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact coordinateEquiv.symm_apply_apply (k x)
  map_add' k l := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change coordinateEquiv.symm (k x + l x) = coordinateEquiv.symm (k x) + coordinateEquiv.symm (l x)
    exact map_add _ _ _
  map_smul' z k := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change coordinateEquiv.symm (z • k x) = z • coordinateEquiv.symm (k x)
    exact map_smul _ _ _

/-- Admissible orbit Hom: the original typed equations applied after the
explicit local assembly. The entries are not 25 unrestricted flavor maps. -/
def statisticsSubmodule : Submodule ℂ (OrbitHom U D up down) :=
  (SixQuarkTypedFlavor.statisticsSubmodule U D up down).comap
    (homEquiv U D up down).symm.toLinearMap

abbrev StatisticsHom := ↥(statisticsSubmodule U D up down)

theorem statistics_iff (k : OrbitHom U D up down) :
    k ∈ statisticsSubmodule U D up down ↔
      ∀ g (t : ∀ i, SixQuarkTypedFlavor.SlotFlavor U D i),
        coordinateEquiv.symm (SixQuarkSpeciesQuotient.transform
          (coordinateEquiv (k (PiTensorProduct.tprod ℂ
            (exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t)))) g) =
          -k (PiTensorProduct.tprod ℂ t) := by
  change (∀ g t, SixQuarkSpeciesQuotient.transform
    (coordinateEquiv (k (PiTensorProduct.tprod ℂ
      (exchangeFlavor g (SixQuarkTypedFlavor.speciesExchange U D g) t)))) g =
        -coordinateEquiv (k (PiTensorProduct.tprod ℂ t))) ↔ _
  constructor
  · intro h g t
    rw [h g t, map_neg, LinearEquiv.symm_apply_apply]
  · intro h g t
    apply coordinateEquiv.symm.injective
    simpa only [map_neg, LinearEquiv.symm_apply_apply] using h g t

def statisticsEquiv : SixQuarkTypedFlavor.StatisticsHom U D up down ≃ₗ[ℂ]
    StatisticsHom U D up down where
  toFun k := ⟨homEquiv U D up down k.val, by
    change (homEquiv U D up down).symm (homEquiv U D up down k.val) ∈
      SixQuarkTypedFlavor.statisticsSubmodule U D up down
    rw [LinearEquiv.symm_apply_apply]
    exact k.property⟩
  invFun k := ⟨(homEquiv U D up down).symm k.val, k.property⟩
  left_inv k := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv k := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' k l := by apply Subtype.ext; exact map_add _ _ _
  map_smul' z k := by apply Subtype.ext; exact map_smul _ _ _

def coefficientEquiv : SixQuarkTypedFlavor.Coefficients U D up down ≃ₗ[ℂ]
    StatisticsHom U D up down :=
  (SixQuarkTypedFlavor.homLinearEquiv U D up down).trans
    (statisticsEquiv U D up down)

def physicalEquiv : DeltaBTwoModelInterface.ModelSector up down ≃ₗ[ℂ]
    StatisticsHom U D up down :=
  (DeltaBTwoFlavorBridge.sectorHomEquiv up down).trans
    (statisticsEquiv U D up down)

theorem physical_assembly_extraction (f : DeltaBTwoModelInterface.ModelSector up down) :
    (physicalEquiv U D up down).symm (physicalEquiv U D up down f) = f :=
  LinearEquiv.symm_apply_apply _ _

theorem physical_extraction_assembly (k : StatisticsHom U D up down) :
    physicalEquiv U D up down ((physicalEquiv U D up down).symm k) = k :=
  LinearEquiv.apply_symm_apply _ _

section ActualFields
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup H) A)
  (b : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup H) B)
  (input : DeltaBTwoModelInterface.Inputs up down a b)

def onFieldsEquiv : SixSlotSpeciesDegree.sector a b ≃ₗ[ℂ]
    StatisticsHom U D up down :=
  (DeltaBTwoFlavorBridge.onFieldsHomEquiv up down a b input).trans
    (statisticsEquiv U D up down)

theorem onFields_reconstruction (f : SixSlotSpeciesDegree.sector a b) :
    (onFieldsEquiv U D up down a b input).symm (onFieldsEquiv U D up down a b input f) = f :=
  LinearEquiv.symm_apply_apply _ _
end ActualFields

end

noncomputable section
abbrev scalar := DeltaBTwoFlavorOneGeneration.scalar

def scalarProbeEquiv : StatisticsHom ℂ ℂ scalar scalar ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (statisticsEquiv ℂ ℂ scalar scalar).symm.trans
    DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv

theorem scalar_finrank : Module.finrank ℂ (StatisticsHom ℂ ℂ scalar scalar) = 2 := by
  rw [scalarProbeEquiv.finrank_eq]
  simp

theorem scalar_physical_agrees (f : DeltaBTwoModelInterface.ModelSector scalar scalar) :
    scalarProbeEquiv (physicalEquiv ℂ ℂ scalar scalar f) =
      DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv f := by
  simp only [scalarProbeEquiv, physicalEquiv, DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end
end Physics.LiSixQuarkResidual
