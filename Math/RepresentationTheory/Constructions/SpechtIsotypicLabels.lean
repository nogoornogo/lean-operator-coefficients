import Math.RepresentationTheory.Constructions.IsotypicClassMap
import TauCeti.RepresentationTheory.Symmetric.Specht.Complex

/-! Partitions label the distinct complex symmetric-group isotypic components,
including arbitrary-dimensional modules and arbitrary multiplicities. -/
namespace Math.SpechtIsotypicLabels
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
variable (d : ℕ)

private instance cardinalNonzero : NeZero (Nat.card (Equiv.Perm (Fin d)) : ℂ) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

def partitionClass (mu : d.Partition) :
    TauCeti.SimpleSubmoduleClasses ℂ[Equiv.Perm (Fin d)] ℂ[Equiv.Perm (Fin d)] :=
  TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses (TauCeti.spechtModuleℂFDRepClass mu)

theorem partitionClass_bijective : Function.Bijective (partitionClass d) :=
  TauCeti.SimpleSubmoduleClasses.bijective_of_injective_of_card_conjClasses_le
    (TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses_injective.comp
      TauCeti.spechtModuleℂFDRepClass_bijective.injective)
    (Nat.card_congr (TauCeti.partitionEquivConjClasses d).symm).le

def partitionEquiv : d.Partition ≃
    TauCeti.SimpleSubmoduleClasses ℂ[Equiv.Perm (Fin d)] ℂ[Equiv.Perm (Fin d)] :=
  Equiv.ofBijective _ (partitionClass_bijective d)

variable {M : Type*} [AddCommGroup M] [Module ℂ[Equiv.Perm (Fin d)] M]

def label (c : isotypicComponents ℂ[Equiv.Perm (Fin d)] M) : d.Partition :=
  (partitionEquiv d).symm (IsotypicClassMap.componentClass c)

theorem label_injective : Function.Injective (label d (M := M)) :=
  (partitionEquiv d).symm.injective.comp IsotypicClassMap.componentClass_injective

/-- The label is the Specht type, not merely an arbitrary injection into partitions. -/
theorem label_simple_iff (N : Submodule ℂ[Equiv.Perm (Fin d)] M)
    [IsSimpleModule ℂ[Equiv.Perm (Fin d)] N] (mu : d.Partition) :
    label d (⟨isotypicComponent ℂ[Equiv.Perm (Fin d)] M N, N, inferInstance, rfl⟩) = mu ↔
      Nonempty (N ≃ₗ[ℂ[Equiv.Perm (Fin d)]]
        Representation.asModule (TauCeti.spechtModuleℂ mu).ρ) := by
  rw [label, IsotypicClassMap.componentClass_simple]
  rw [Equiv.symm_apply_eq]
  change TauCeti.simpleModuleClass ℂ[Equiv.Perm (Fin d)] N = partitionClass d mu ↔ _
  rw [partitionClass, TauCeti.spechtModuleℂFDRepClass_def,
    TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses_mk]
  exact TauCeti.simpleModuleClass_eq_iff

/-- Only partitions actually occurring in the module are retained. -/
def supportedEquiv : isotypicComponents ℂ[Equiv.Perm (Fin d)] M ≃
    Set.range (label d (M := M)) :=
  Equiv.ofInjective _ (label_injective d)

theorem finite_components : Finite (isotypicComponents ℂ[Equiv.Perm (Fin d)] M) :=
  Finite.of_injective _ (label_injective d)

end
end Math.SpechtIsotypicLabels
