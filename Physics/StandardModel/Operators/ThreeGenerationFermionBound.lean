import Physics.StandardModel.Operators.BnvMixedInput
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.ExteriorPower.Basic

namespace GUT.ThreeGenerationFermionBound
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput DeltaLOneSignedFields
open scoped TensorProduct
abbrev Flavor (_ : Species) := Fin 3 → ℂ
local instance (u : Species) : FiniteDimensional ℂ (DeltaLOneSignedFields.Field (F := Flavor) u) := by
  fin_cases u <;> dsimp [DeltaLOneSignedFields.Field,Flavor,GaugeCarrier] <;> infer_instance
abbrev Fields := ∀ u : Species, DeltaLOneSignedFields.Field (F := Flavor) u
local instance : AddCommGroup Fields := inferInstance
local instance : FiniteDimensional ℂ Fields := inferInstance

theorem species_dimension (u : Species) :
    Module.finrank ℂ (DeltaLOneSignedFields.Field (F := Flavor) u) =
      (![36,18,18,12,6,36,18,18,12,6] : Fin 10 → ℕ) u := by
  fin_cases u <;>
    simp [DeltaLOneSignedFields.Field,Flavor,GaugeCarrier,StandardSMGaugeTensor.Quark,
      SMEpsilonTensor.Color,SMEpsilonTensor.Weak,WeylSpinor.Space,
      Module.finrank_tensorProduct,Subspace.dual_finrank_eq]

theorem total_dimension : Module.finrank ℂ Fields = 180 := by
  rw [Module.finrank_pi_fintype]
  simp_rw [species_dimension]
  decide +kernel

theorem exterior_zero (n : ℕ) (hn : 180 < n) (x : ⋀[ℂ]^n Fields) : x = 0 :=
  _root_.exteriorPower.eq_zero_of_finrank_lt n (by rw [total_dimension]; exact hn) x

variable {H : Type*} [Group H]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ H (Flavor u))
  (scalarFlavor : ∀ u, Representation ℂ H (S u))

theorem coefficients_zero (n m : ℕ) (hn : 180 < n)
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m) : f = 0 := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  rw [exterior_zero n hn x]
  simp

theorem nonzero_degree_bound {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m) (hf : f ≠ 0) : n ≤ 180 := by
  by_contra hn
  exact hf (coefficients_zero flavor scalarFlavor n m (by omega) f)

def multiplicity {n : ℕ} (p : Fin n → Species) (u : Species) : ℕ :=
  (Finset.univ.filter (fun i => p i = u)).card

theorem content_count_bound {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m) (hf : f ≠ 0)
    (p : Fin n → Species) (u : Species) : multiplicity p u ≤ 180 := by
  have hn := nonzero_degree_bound flavor scalarFlavor f hf
  have hc : multiplicity p u ≤ n := by
    unfold multiplicity
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- A finite count universe is derived from an actual nonzero coefficient. -/
def finiteContent {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m) (hf : f ≠ 0)
    (p : Fin n → Species) : Species → Fin 181 := fun u =>
  ⟨multiplicity p u,by have := content_count_bound flavor scalarFlavor f hf p u; omega⟩
end
end GUT.ThreeGenerationFermionBound
