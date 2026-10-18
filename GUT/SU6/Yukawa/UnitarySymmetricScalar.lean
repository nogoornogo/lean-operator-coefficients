import Physics.FieldTheory.Yukawa.ContinuousSymmetricScalar
import GUT.SU6.Representations.ContinuousUnitaryConstructions

open Math

/-!
# A continuous unitary SU(6) scalar completion

The scalar representation and its full-group Yukawa coupling depend only
on the fermion representation. The desired restricted mass specifies the
vacuum, whose invariance is proved from the mass invariance. There is no
claim of a scalar potential, a preferred Higgs multiplet, or an exact
identification of the vacuum stabilizer with the declared unbroken group.
-/

set_option autoImplicit false

namespace GUT.UnitarySymmetricScalar

noncomputable section

open InvariantWeylMass WeylYukawaMass ContinuousRepresentationScope
open ContinuousSymmetricScalar ContinuousUnitaryConstructions
open scoped TensorProduct

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (rho : Representation ℂ ActualRestriction.SU6 V) (h : IsJointlyContinuous rho)

def model : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation :=
  ContinuousSU6Unitarization.model (seedRho rho) (seed_jointlyContinuous rho h)

def algebraEquiv : Representation.Equiv (SymmetricScalarYukawa.scalarRho rho) (model rho h).rho :=
  (seedEquiv rho).trans
    (ContinuousSU6Unitarization.modelEquiv (seedRho rho) (seed_jointlyContinuous rho h))

def yukawa : EquivariantYukawa (S := (model rho h).V) (model rho h).rho rho where
  toLinearMap := (SymmetricScalarYukawa.yukawa rho).toLinearMap.comp
    (algebraEquiv rho h).symm.toLinearEquiv.toLinearMap
  symmetric s := (SymmetricScalarYukawa.yukawa rho).symmetric ((algebraEquiv rho h).symm s)
  invariant g s x y := by
    change (SymmetricScalarYukawa.yukawa rho).toLinearMap
      ((algebraEquiv rho h).symm ((model rho h).rho g s)) (rho g x) (rho g y) = _
    have he : (algebraEquiv rho h).symm ((model rho h).rho g s) =
        SymmetricScalarYukawa.scalarRho rho g ((algebraEquiv rho h).symm s) :=
      Representation.IntertwiningMap.isIntertwining _ _
        (algebraEquiv rho h).symm.toIntertwiningMap g s
    rw [he]
    exact (SymmetricScalarYukawa.yukawa rho).invariant g _ x y

variable {K : Type*} [Group K]

def vacuum (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f)) :
    (model rho h).V :=
  algebraEquiv rho h (SymmetricScalarYukawa.vacuum rho f B)

theorem vacuum_fixed_iff (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f))
    (g : ActualRestriction.SU6) :
    (model rho h).rho g (vacuum rho h f B) = vacuum rho h f B ↔
      ∀ x y, B.form (rho g x) (rho g y) = B.form x y := by
  have he : (model rho h).rho g (vacuum rho h f B) =
      algebraEquiv rho h (SymmetricScalarYukawa.scalarRho rho g
        (SymmetricScalarYukawa.vacuum rho f B)) :=
    (Representation.IntertwiningMap.isIntertwining _ _
      (algebraEquiv rho h).toIntertwiningMap g _).symm
  rw [he]
  change (algebraEquiv rho h).toLinearEquiv _ = (algebraEquiv rho h).toLinearEquiv _ ↔ _
  rw [(algebraEquiv rho h).toLinearEquiv.injective.eq_iff]
  exact SymmetricScalarYukawa.fixed_iff rho (SymmetricScalarYukawa.vacuum rho f B) g

theorem vacuum_fixed (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f)) (k : K) :
    (model rho h).rho (f k) (vacuum rho h f B) = vacuum rho h f B := by
  exact (Representation.IntertwiningMap.isIntertwining _ _
    (algebraEquiv rho h).toIntertwiningMap (f k) _).symm.trans
      (congrArg (algebraEquiv rho h) (SymmetricScalarYukawa.vacuum_fixed rho f B k))

@[simp] theorem yukawa_vacuum (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f)) :
    (yukawa rho h).toLinearMap (vacuum rho h f B) = B.form := by
  change (SymmetricScalarYukawa.yukawa rho).toLinearMap
    ((algebraEquiv rho h).toLinearEquiv.symm
      ((algebraEquiv rho h).toLinearEquiv (SymmetricScalarYukawa.vacuum rho f B))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem vacuum_nonzero (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f))
    (hB : B.form ≠ 0) : vacuum rho h f B ≠ 0 := by
  intro hv
  apply hB
  rw [← yukawa_vacuum rho h f B, hv, map_zero]

theorem yukawa_nonzero (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f))
    (hB : B.form ≠ 0) : (yukawa rho h).toLinearMap ≠ 0 := by
  intro hz
  have he := LinearMap.congr_fun hz (vacuum rho h f B)
  rw [yukawa_vacuum, LinearMap.zero_apply] at he
  exact hB he

theorem tensor_nonzero (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f))
    (hB : B.form ≠ 0) : (yukawa rho h).tensor ≠ 0 := by
  intro hz
  apply hB
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  have he := LinearMap.congr_fun hz ((vacuum rho h f B ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y)
  simpa only [EquivariantYukawa.tensor_tmul, yukawa_vacuum, LinearMap.zero_apply] using he

def inducedMass (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f)) :
    SymmetricMass (rho.comp f) :=
  atVacuumOn (SymmetricMass.zero rho) (yukawa rho h) f (vacuum rho h f B)
    (vacuum_fixed rho h f B)

theorem inducedMass_eq (f : K →* ActualRestriction.SU6) (B : SymmetricMass (rho.comp f)) :
    inducedMass rho h f B = B := by
  have he := yukawa_vacuum rho h f B
  cases B
  simp only [inducedMass, atVacuumOn, SymmetricMass.zero, zero_add, he]

end

end GUT.UnitarySymmetricScalar
