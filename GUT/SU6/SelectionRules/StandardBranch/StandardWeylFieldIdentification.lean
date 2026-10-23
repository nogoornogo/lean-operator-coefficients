import GUT.SU6.SelectionRules.Benchmarks.ContinuousWeylBenchmark

open Math

/-!
# Equality of the two canonical field constructions at the standard pair

The standard and arbitrary-cocharacter APIs use identical actual charge
sectors. Their bundled unitary representations agree, not just their traces.
This permits transporting a given mass without replacing it by another one.
-/

set_option autoImplicit false

namespace GUT.StandardWeylFieldIdentification

noncomputable section

open StandardWeylMassSource PhysicalMassSpectrumBridge PhysicalChargeResolvedBridge
open PhysicalChargedCharacterBridge StandardPhysicalCharacterBridge
open StandardPhysicalSource Physics.UnitaryVirtualRealization
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)

variable {H : Type*} [CommGroup H]

theorem sector_rho_eq (s : ChargedContinuousUnitarySummand
    (FiniteAbelianChargeSectors.ChargeLabel H)) :
    chargedPhysicalRho (-2) 3 s = chargedProductRho 1 s := by
  ext g v
  rcases g with ⟨x, h⟩
  simp [chargedPhysicalRho, chargedProductRho]

theorem sector_eq (s : ChargedContinuousUnitarySummand
    (FiniteAbelianChargeSectors.ChargeLabel H)) :
    chargedPhysicalUnitaryRepresentation (-2) 3 s = sectorUnitaryRepresentation s := by
  unfold chargedPhysicalUnitaryRepresentation sectorUnitaryRepresentation
  simp only [sector_rho_eq]

theorem source_eq (source : FiniteChargedContinuousUnitarySource
    (FiniteAbelianChargeSectors.ChargeLabel H)) :
    sourceUnitaryRepresentation (-2) 3 source = unitarySource source := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change _ :: sourceUnitaryRepresentation (-2) 3 source = _ :: unitarySource source
      rw [ih, sector_eq]

theorem fields_eq (matter : OrdinaryAbelianSource H) :
    ordinaryPositiveRepresentation (-2) 3 matter = ordinaryFields matter := by
  unfold ordinaryPositiveRepresentation ordinaryUnitaryVirtualSource ordinaryFields fields
  rw [source_eq]

theorem continuous_fields_eq (matter : OrdinaryAbelianSource H) :
    ordinaryPositiveRepresentation ConcreteStandardGeometry.geometry.hyperchargePair.1
      ConcreteStandardGeometry.geometry.hyperchargePair.2 matter = ordinaryFields matter := by
  rw [ConcreteStandardGeometry.hyperchargePair_eq_standard]
  exact fields_eq matter

end

end GUT.StandardWeylFieldIdentification
