import Math.RepresentationTheory.Characters.UnitaryCharacterSpectrum
import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.LieGroups.Torus.CircleTorusCharacterLattice

/-! A finite integer Laurent presentation of every continuous finite-dimensional
torus character. Weights are constructed, not supplied as multiplicities. -/
namespace Math.FiniteTorusPresentation
set_option autoImplicit false
noncomputable section
open Representation ContinuousRepresentationScope CircleTorusCharacterLattice
open UnitaryCharacterProfile
variable {d V : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ (Torus d) V)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho) (hr : IsJointlyContinuous rho)

omit [Fintype d] [DecidableEq d] in
include hr in
theorem active_continuous (chi : Active rho) : Continuous chi.val := by
  classical
  obtain ⟨v,hv,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot chi.property
  let b := Module.finBasis ℂ V
  have hc : b.repr v ≠ 0 := fun he => hne (b.repr.injective (he.trans (map_zero b.repr).symm))
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hc
  have hi' : b.repr v i ≠ 0 := by simpa using hi
  have horbit : Continuous (fun t => (b.repr v i)⁻¹ * b.repr (rho t v) i) :=
    continuous_const.mul ((b.coord i).continuous_of_finiteDimensional.comp (hr.orbit v))
  apply continuous_induced_rng.mpr
  exact horbit.congr (fun t => by
    have he : rho t v = (chi.val t : ℂ) • v := hv t
    rw [he,map_smul,Finsupp.smul_apply,smul_eq_mul]
    field_simp
    rfl)

def activeCharacter (chi : Active rho) : Torus d →ₜ* Circle :=
  ⟨chi.val,active_continuous rho hr chi⟩

def weight (chi : Active rho) : d → ℤ :=
  (existsUnique_eq_torusCharacter (activeCharacter rho hr chi)).choose

theorem weight_character (chi : Active rho) (t : Torus d) :
    torusCharacter (weight rho hr chi) t = chi.val t :=
  congrArg (fun f : Torus d →ₜ* Circle => f t)
    (existsUnique_eq_torusCharacter (activeCharacter rho hr chi)).choose_spec.1.symm

def coefficients : (d → ℤ) →₀ ℤ :=
  letI := activeFintype rho hu
  ∑ chi : Active rho, Finsupp.single (weight rho hr chi) (Module.finrank ℂ (space rho chi.val) : ℤ)

theorem presentation (t : Torus d) :
    (coefficients rho hu hr).sum (fun w c => (c : ℂ) * (torusCharacter w t : ℂ)) = rho.character t := by
  classical
  let := activeFintype rho hu
  rw [← UnitaryCharacterSpectrum.profile_eval rho hu t]
  unfold coefficients profile
  rw [← Finsupp.sum_finsetSum_index, ← Finsupp.sum_finsetSum_index]
  · simp only [Finsupp.sum_single_index,Int.cast_zero,Nat.cast_zero,zero_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro chi _
    exact congrArg (fun z : Circle => (Module.finrank ℂ (space rho chi.val) : ℂ) * (z : ℂ))
      (weight_character rho hr chi t)
  all_goals intros; simp [add_mul]


section ArbitraryContinuous
local instance torusMeasurable : MeasurableSpace (Torus d) := borel (Torus d)
local instance torusBorel : BorelSpace (Torus d) := ⟨rfl⟩
variable {K : Type*} [Group K] [TopologicalSpace K]
  (a : Representation ℂ K V) (ha : IsJointlyContinuous a) (j : Torus d →ₜ* K)

def inverseTorus : Torus d →ₜ* Torus d where
  toMonoidHom :=
    { toFun := fun t => t⁻¹
      map_one' := inv_one
      map_mul' := fun x y => by simp [mul_comm] }
  continuous_toFun := continuous_inv

abbrev inverseRestriction := a.comp ((j.comp inverseTorus).toMonoidHom)
def inverseBasis := Module.finBasis ℂ V

omit [Fintype d] [DecidableEq d] in
include ha in
theorem inverse_coordinates (i k : Fin (Module.finrank ℂ V)) :
    Continuous (fun t => (inverseBasis (V := V)).coord i
      (inverseRestriction a j t (inverseBasis (V := V) k))) :=
  (inverseBasis (V := V)).coord i |>.continuous_of_finiteDimensional.comp
    (((ha.comp (j.comp inverseTorus)).orbit (inverseBasis (V := V) k)))

abbrev inverseModel := FiniteBasisUnitaryModel.model (inverseBasis (V := V)) (inverseRestriction a j)
  (inverse_coordinates a ha j)

omit [Fintype d] [DecidableEq d] in
theorem inverseModel_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (inverseModel a ha j).toRepresentation :=
  FiniteBasisUnitaryModel.model_inner _ _ _

omit [Fintype d] [DecidableEq d] in
theorem inverseModel_continuous : IsJointlyContinuous (inverseModel a ha j).toRepresentation :=
  FiniteBasisUnitaryModel.model_jointlyContinuous _ _ _

def inverseCoefficients : (d → ℤ) →₀ ℤ :=
  coefficients (inverseModel a ha j).toRepresentation (inverseModel_unitary a ha j) (inverseModel_continuous a ha j)

theorem inverse_presentation (t : Torus d) :
    (inverseCoefficients a ha j).sum (fun w c => (c : ℂ) * (torusCharacter w t : ℂ)) =
      a.character ((j t)⁻¹) := by
  rw [inverseCoefficients,presentation]
  rw [← Representation.char_iso (FiniteBasisUnitaryModel.modelEquiv (inverseBasis (V := V))
    (inverseRestriction a j) (inverse_coordinates a ha j))]
  change LinearMap.trace ℂ V (a (j (t⁻¹))) = _
  rw [map_inv]
  rfl
end ArbitraryContinuous

end
end Math.FiniteTorusPresentation
