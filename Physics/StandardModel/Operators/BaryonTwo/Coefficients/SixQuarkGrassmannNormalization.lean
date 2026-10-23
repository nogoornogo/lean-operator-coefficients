import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalBasis
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates
import Physics.FieldTheory.Spinor.Weyl.RightWeylChargeConjugation
import Math.LinearAlgebra.Selection.GrassmannCoefficient

open Math

/-! Explicit Grassmann polynomials, determinant pairing, species factorial
and generator-order conventions for the all-right degree (2,4) sector. -/
namespace Physics.SixQuarkGrassmannNormalization
set_option autoImplicit false
noncomputable section
open Module SixQuarkInvariant SixQuarkTwoCoordinates SixQuarkConventionalBasis
open SixQuarkSpeciesQuotient
open RightWeylChargeConjugation
open scoped TensorProduct
abbrev Fields := SixSlotAlternation.Fields Quark Quark
variable {I : Type*} [Fintype I] (b : Basis I ℂ Fields)
attribute [local irreducible] orderedLift SixSlotAlternation.ordered
  GrassmannCoefficient.pairingEquiv MultilinearMap.alternatization
  SixSlotAlternation.alternating SixSlotAlternation.coefficient

/-- An ordered contraction summed against products of coordinate generators,
not an exterior functional relabeled as a Grassmann polynomial. -/
def orderedPolynomial (f : Coefficient) : ⋀[ℂ]^6 (Module.Dual ℂ Fields) :=
  GrassmannCoefficient.polynomial b 6 (SixSlotAlternation.ordered (orderedLift f))

/-- The polynomial of an intrinsic sector coefficient via the canonical dual
exterior pairing. -/
def sectorPolynomial (f : Sector) : ⋀[ℂ]^6 (Module.Dual ℂ Fields) :=
  (GrassmannCoefficient.pairingEquiv b 6).symm f.1.toLinearMap

attribute [local irreducible] orderedPolynomial sectorPolynomial

theorem pairing_ordered (f : Coefficient) (hf : IsInvariant f) :
    exteriorPower.pairingDual ℂ Fields 6 (orderedPolynomial b f) =
      (descend f hf).1.toLinearMap := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply,
    Representation.IntertwiningMap.coe_toLinearMap, descend]
  rw [SixSlotAlternation.coefficient_apply_ιMulti]
  rw [orderedIntertwiner_toLinearMap]
  unfold orderedPolynomial SixSlotAlternation.alternating
  exact GrassmannCoefficient.polynomial_pairing b 6
    (SixSlotAlternation.ordered (orderedLift f)) v

theorem ordered_eq_sector (f : Coefficient) (hf : IsInvariant f) :
    orderedPolynomial b f = sectorPolynomial b (descend f hf) := by
  apply (GrassmannCoefficient.pairingEquiv b 6).injective
  rw [sectorPolynomial, GrassmannCoefficient.pairingEquiv_apply,
    LinearEquiv.apply_symm_apply]
  exact pairing_ordered b f hf

theorem sectorPolynomial_add (f g : Sector) :
    sectorPolynomial b (f + g) = sectorPolynomial b f + sectorPolynomial b g := by
  unfold sectorPolynomial
  change (GrassmannCoefficient.pairingEquiv b 6).symm
    (f.1.toLinearMap + g.1.toLinearMap) = _
  exact map_add _ _ _

theorem sectorPolynomial_smul (z : ℂ) (f : Sector) :
    sectorPolynomial b (z • f) = z • sectorPolynomial b f := by
  unfold sectorPolynomial
  change (GrassmannCoefficient.pairingEquiv b 6).symm (z • f.1.toLinearMap) = _
  exact map_smul _ _ _

/-- Changing the coordinate basis changes only the presentation of the same
Grassmann element; there is no additional normalization choice. -/
theorem basis_independent {J : Type*} [Fintype J]
    (c : Basis J ℂ Fields) (f : Coefficient) (hf : IsInvariant f) :
    orderedPolynomial b f = orderedPolynomial c f := by
  apply (GrassmannCoefficient.pairingEquiv b 6).injective
  simp only [GrassmannCoefficient.pairingEquiv_apply]
  exact (pairing_ordered b f hf).trans (pairing_ordered c f hf).symm

attribute [local irreducible] orderedO2 orderedO3 descend

theorem O1_fourComponent (v : Fin 6 → SMEpsilonTensor.Color) (s : Fin 6 → Spin) :
    orderedO1 (fun i => v i ⊗ₜ[ℂ] s i) =
      -DeltaBTwoContractionRelations.colorSSS (v 0) (v 2) (v 1) (v 3) (v 4) (v 5) *
        (diquark (embedRight (s 0)) (embedRight (s 2)) *
          diquark (embedRight (s 1)) (embedRight (s 3)) *
          diquark (embedRight (s 4)) (embedRight (s 5))) := by
  rw [orderedO1_apply]
  simp only [DeltaBTwoContractionRelations.orderedO1Value, right_diquark]

theorem O2_fourComponent (v : Fin 6 → SMEpsilonTensor.Color) (s : Fin 6 → Spin) :
    orderedO2 (fun i => v i ⊗ₜ[ℂ] s i) =
      DeltaBTwoContractionRelations.colorSSS (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) *
        (diquark (embedRight (s 0)) (embedRight (s 1)) *
          diquark (embedRight (s 2)) (embedRight (s 3)) *
          diquark (embedRight (s 4)) (embedRight (s 5))) := by
  rw [orderedO2_apply]
  simp only [DeltaBTwoContractionRelations.orderedO2Value, right_diquark]

theorem O3_fourComponent (v : Fin 6 → SMEpsilonTensor.Color) (s : Fin 6 → Spin) :
    orderedO3 (fun i => v i ⊗ₜ[ℂ] s i) =
      DeltaBTwoContractionRelations.colorAAS (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) *
        (diquark (embedRight (s 0)) (embedRight (s 1)) *
          diquark (embedRight (s 2)) (embedRight (s 3)) *
          diquark (embedRight (s 4)) (embedRight (s 5))) := by
  rw [orderedO3_apply]
  simp only [DeltaBTwoContractionRelations.orderedO3Value, right_diquark]

/-- Conventional two-coefficient reconstruction of the actual Grassmann
polynomial attached to any intrinsic physical sector coefficient. -/
theorem grassmann_reconstruct (f : Sector) :
    sectorPolynomial b f =
      (SixQuarkConventionalCoordinates.conventionalEquiv f 0) •
        orderedPolynomial b orderedO3 +
      (SixQuarkConventionalCoordinates.conventionalEquiv f 1) •
        orderedPolynomial b orderedO2 := by
  conv_lhs => rw [SixQuarkConventionalCoordinates.reconstruct f]
  rw [sectorPolynomial_add, sectorPolynomial_smul, sectorPolynomial_smul]
  have h3 : sectorPolynomial b O3 = orderedPolynomial b orderedO3 := by
    change sectorPolynomial b (descend orderedO3 orderedO3_invariant) = _
    exact (ordered_eq_sector b orderedO3 orderedO3_invariant).symm
  have h2 : sectorPolynomial b O2 = orderedPolynomial b orderedO2 := by
    change sectorPolynomial b (descend orderedO2 orderedO2_invariant) = _
    exact (ordered_eq_sector b orderedO2 orderedO2_invariant).symm
  exact congrArg₂ (fun x y => x + y)
    (congrArg (fun P => (SixQuarkConventionalCoordinates.conventionalEquiv f 0) • P) h3)
    (congrArg (fun P => (SixQuarkConventionalCoordinates.conventionalEquiv f 1) • P) h2)

theorem grassmann_reconstruct_chiral (f : Sector) :
    sectorPolynomial b f =
      (SixQuarkConventionalCoordinates.chiralEquiv f 0) •
        sectorPolynomial b SixQuarkConventionalCoordinates.Q1 +
      (SixQuarkConventionalCoordinates.chiralEquiv f 1) •
        sectorPolynomial b SixQuarkConventionalCoordinates.Q4 := by
  conv_lhs => rw [SixQuarkConventionalCoordinates.reconstruct_chiral f]
  rw [sectorPolynomial_add, sectorPolynomial_smul, sectorPolynomial_smul]

theorem ordered_monomial [LinearOrder I] (f : Coefficient) (hf : IsInvariant f)
    (s : Set.powersetCard I 6) :
    (b.dualBasis.exteriorPower 6).repr (orderedPolynomial b f) s =
      (descend f hf).1 (b.exteriorPower 6 s) := by
  unfold orderedPolynomial
  rw [GrassmannCoefficient.polynomial_coordinate]
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  symm
  unfold descend
  change SixSlotAlternation.coefficient _ _ _ _ = _
  rw [SixSlotAlternation.coefficient_apply_ιMulti, orderedIntertwiner_toLinearMap]
  unfold SixSlotAlternation.alternating
  rfl

/-- The factorial is species-wise 2! 4!, not 6!. -/
theorem species_factorial : Nat.factorial 2 * Nat.factorial 4 = 48 := by decide

theorem normalized_polynomial (f : admissible) :
    orderedPolynomial b f.1 = (48 : ℂ) • sectorPolynomial b (liftCoefficient f) := by
  apply (GrassmannCoefficient.pairingEquiv b 6).injective
  rw [map_smul, sectorPolynomial, LinearEquiv.apply_symm_apply,
    GrassmannCoefficient.pairingEquiv_apply]
  rw [pairing_ordered b f.1 f.2.1]
  unfold liftCoefficient descend
  ext v
  simp

/-- Moving the second up field past the first down field changes the sign.
The reference slots are u,d,u,d,d,d; species-block order is u,u,d,d,d,d. -/
theorem species_block_sign (f : Coefficient) (hf : IsInvariant f)
    (u : Fin 2 → Quark) (d : Fin 4 → Quark) :
    exteriorPower.pairingDual ℂ Fields 6 (orderedPolynomial b f)
      (exteriorPower.ιMulti ℂ 6
        ![(u 0,0),(u 1,0),(0,d 0),(0,d 1),(0,d 2),(0,d 3)]) =
      -(descend f hf).1 (exteriorPower.ιMulti ℂ 6
        (SixSlotAlternation.slots (u 0) (u 1) (d 0) (d 1) (d 2) (d 3))) := by
  rw [pairing_ordered b f hf]
  have hv : ![(u 0,(0 : Quark)),(u 1,0),(0,d 0),(0,d 1),(0,d 2),(0,d 3)] =
      SixSlotAlternation.slots (u 0) (u 1) (d 0) (d 1) (d 2) (d 3) ∘
        Equiv.swap 1 2 := by
    ext i <;> fin_cases i <;>
      simp [SixSlotAlternation.slots, Equiv.swap_apply_def]
  rw [hv, (exteriorPower.ιMulti ℂ 6).map_swap _ (by decide : (1 : Fin 6) ≠ 2),
    map_neg]
  rfl

end
end Physics.SixQuarkGrassmannNormalization
