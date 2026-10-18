import Math.RepresentationTheory.Multiplicity.MultiplicitySpecialCentralizer

/-!
# U/SU centralizer classification from a unitary representation alone

The multiplicities, simple constituents, and isometric decomposition are
constructed. There is no supplied centralizer-classification certificate.
The group may be infinite and need not carry a topology.
-/

namespace Math.UnitaryMultiplicity

noncomputable section

open scoped MonoidAlgebra

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E) (h : IsUnitaryRepresentation rho)

local instance componentsFintype : Fintype (isotypicComponents ℂ[G] rho.asModule) := by
  let := MultiplicityCommutant.finite_components rho
  exact Fintype.ofFinite _

/-- The factors have the multiplicities of the actual isotypic components. -/
abbrev unitaryFactors := Π c : isotypicComponents ℂ[G] rho.asModule,
  Matrix.unitaryGroup (Fin ((multiplicityModel rho h).multiplicity c)) ℂ

/-- The exponents are the dimensions of the actual simple constituents. -/
def determinantCharacter : unitaryFactors rho h →* ℂ :=
  MultiplicitySpecialCentralizer.weightedDet rho (multiplicityModel rho h)

/-- The full kernel, including any finite or disconnected components. -/
def specialFactors : Subgroup (unitaryFactors rho h) := (determinantCharacter rho h).ker

/-- Classification of the actual U centralizer, continuous in both directions. -/
def unitaryCentralizerEquiv :
    UnitaryCentralizerTransport.unitaryCentralizer rho ≃ₜ* unitaryFactors rho h :=
  MultiplicityUnitaryCentralizer.unitaryCentralizerEquiv rho (multiplicityModel rho h) h

/-- Classification of the actual SU centralizer by the weighted determinant kernel. -/
def specialCentralizerEquiv :
    UnitaryCentralizerTransport.specialCentralizer rho ≃ₜ* specialFactors rho h :=
  MultiplicitySpecialCentralizer.specialCentralizerEquiv rho (multiplicityModel rho h) h

end

end Math.UnitaryMultiplicity
