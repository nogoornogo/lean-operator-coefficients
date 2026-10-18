import Math.RepresentationTheory.Unitary.UnitaryIntertwiner
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Determinant

/-!
# Topological transport of U and SU centralizers

An equivariant Hilbert-space isometry conjugates the actual unitary
centralizers, in both directions continuously. The same construction
restricts to determinant one. These statements do not yet identify a
centralizer with the product of multiplicity unitary groups.
-/

namespace Math.UnitaryCentralizerTransport

noncomputable section

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual unitary operators commuting with every represented group element. -/
def unitaryCentralizer (rho : Representation ℂ G E) : Subgroup (unitary (E →L[ℂ] E)) where
  carrier := {u | ∀ g, Commute (u : E →L[ℂ] E) (rho g).toContinuousLinearMap}
  one_mem' := fun _ => Commute.one_left _
  mul_mem' ha hb g := (ha g).mul_left (hb g)
  inv_mem' {u} hu g :=
    (show Commute (Unitary.toUnits u : E →L[ℂ] E) (rho g).toContinuousLinearMap
      from hu g).units_inv_left

/-- Isometric conjugation is a two-sided continuous group isomorphism on U. -/
def unitaryConj (e : E ≃ₗᵢ[ℂ] F) :
    unitary (E →L[ℂ] E) ≃ₜ* unitary (F →L[ℂ] F) where
  toMulEquiv := (Unitary.mapEquiv
    { e.conjStarAlgEquiv.toMulEquiv with map_star' := map_star e.conjStarAlgEquiv }).toMulEquiv
  continuous_toFun := (e.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.toContinuousLinearEquiv.conjContinuousAlgEquiv.symm.continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp]
theorem unitaryConj_apply (e : E ≃ₗᵢ[ℂ] F) (u : unitary (E →L[ℂ] E)) (y : F) :
    (unitaryConj e u : F →L[ℂ] F) y = e ((u : E →L[ℂ] E) (e.symm y)) := rfl

variable {rho : Representation ℂ G E} {sigma : Representation ℂ G F}

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem symm_intertwines (e : E ≃ₗᵢ[ℂ] F)
    (he : ∀ g x, e (rho g x) = sigma g (e x)) (g : G) (y : F) :
    e.symm (sigma g y) = rho g (e.symm y) := by
  apply e.injective
  simp [he]

theorem unitaryConj_mem (e : E ≃ₗᵢ[ℂ] F)
    (he : ∀ g x, e (rho g x) = sigma g (e x))
    {u : unitary (E →L[ℂ] E)} (hu : u ∈ unitaryCentralizer rho) :
    unitaryConj e u ∈ unitaryCentralizer sigma := by
  intro g
  ext y
  change e ((u : E →L[ℂ] E) (e.symm (sigma g y))) =
    sigma g (e ((u : E →L[ℂ] E) (e.symm y)))
  rw [symm_intertwines e he]
  rw [show (u : E →L[ℂ] E) (rho g (e.symm y)) =
    rho g ((u : E →L[ℂ] E) (e.symm y)) from
    congrArg (fun T : E →L[ℂ] E => T (e.symm y)) (hu g).eq]
  exact he g _

/-- The actual U centralizers are isomorphic as topological groups. -/
def unitaryCentralizerEquiv (e : E ≃ₗᵢ[ℂ] F)
    (he : ∀ g x, e (rho g x) = sigma g (e x)) :
    unitaryCentralizer rho ≃ₜ* unitaryCentralizer sigma where
  toFun u := ⟨unitaryConj e u.1, unitaryConj_mem e he u.2⟩
  invFun u := ⟨unitaryConj e.symm u.1,
    unitaryConj_mem e.symm (symm_intertwines e he) u.2⟩
  left_inv u := by
    apply Subtype.ext
    exact (unitaryConj e).left_inv u.1
  right_inv u := by
    apply Subtype.ext
    exact (unitaryConj e).right_inv u.1
  map_mul' u v := Subtype.ext ((unitaryConj e).map_mul u.1 v.1)
  continuous_toFun := ((unitaryConj e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((unitaryConj e.symm).continuous.comp continuous_subtype_val).subtype_mk _

/-- Determinants are those of the actual operators, not separately assigned coordinates. -/
theorem det_unitaryConj (e : E ≃ₗᵢ[ℂ] F) (u : unitary (E →L[ℂ] E)) :
    LinearMap.det (unitaryConj e u : F →L[ℂ] F).toLinearMap =
      LinearMap.det (u : E →L[ℂ] E).toLinearMap :=
  LinearMap.det_conj _ e.toLinearEquiv

/-- Determinant on the actual U centralizer. -/
def determinant (rho : Representation ℂ G E) : unitaryCentralizer rho →* ℂ where
  toFun u := LinearMap.det (u.1 : E →L[ℂ] E).toLinearMap
  map_one' := LinearMap.det.map_one
  map_mul' _ _ := LinearMap.det.map_mul _ _

/-- The actual SU centralizer, expressed as the determinant-one subgroup of the U centralizer. -/
def specialCentralizer (rho : Representation ℂ G E) : Subgroup (unitaryCentralizer rho) :=
  (determinant rho).ker

/-- The actual SU centralizers are isomorphic as topological groups as well. -/
def specialCentralizerEquiv (e : E ≃ₗᵢ[ℂ] F)
    (he : ∀ g x, e (rho g x) = sigma g (e x)) :
    specialCentralizer rho ≃ₜ* specialCentralizer sigma := by
  let f := unitaryCentralizerEquiv e he
  have hf (u : specialCentralizer rho) : f u.1 ∈ specialCentralizer sigma := by
    change LinearMap.det (unitaryConj e u.1.1 : F →L[ℂ] F).toLinearMap = 1
    rw [det_unitaryConj]
    exact u.2
  have hf' (u : specialCentralizer sigma) : f.symm u.1 ∈ specialCentralizer rho := by
    change LinearMap.det (unitaryConj e.symm u.1.1 : E →L[ℂ] E).toLinearMap = 1
    rw [det_unitaryConj]
    exact u.2
  exact
    { toFun := fun u => ⟨f u.1, hf u⟩
      invFun := fun u => ⟨f.symm u.1, hf' u⟩
      left_inv := fun u => Subtype.ext (f.left_inv u.1)
      right_inv := fun u => Subtype.ext (f.right_inv u.1)
      map_mul' := fun u v => Subtype.ext (f.map_mul u.1 v.1)
      continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (f.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

end

end Math.UnitaryCentralizerTransport
