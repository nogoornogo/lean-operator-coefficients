import Math.LieGroups.Spin.CliffordCovariance
import Math.LinearAlgebra.Exterior.PolarizedExteriorAction

/-! Compare the actual SU(5) lift and the exterior action on Clifford
generators. This does not discard the scalar ambiguity between implementers. -/

set_option autoImplicit false

namespace Math.CompactSpin.ExteriorComparison

noncomputable section

open Polarized
open scoped Matrix

abbrev P (n : ℕ) := HalfSpin.polarization n

theorem W_fst (n : ℕ) (x : (P n).W) : (x.val).1 = 0 := by
  have h := x.property
  simpa only [P, HalfSpin.polarization, TauCeti.splitEvenPolarization_W,
    Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top, and_true] using h

theorem W'_snd (n : ℕ) (y : (P n).W') : (y.val).2 = 0 := by
  have h := y.property
  simpa only [P, HalfSpin.polarization, TauCeti.splitEvenPolarization_W',
    Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top, true_and] using h

def WCoordinates (n : ℕ) : (P n).W ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun x := x.val.2
  invFun z := ⟨(0, z), by simp [P, HalfSpin.polarization]⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext (W_fst n x).symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def WAction {n : ℕ} (g : SpecialUnitaryRealification.Source n) : (P n).W ≃ₗ[ℂ] (P n).W :=
  (WCoordinates n).trans ((SpecialUnitaryRealification.complexAction g).trans (WCoordinates n).symm)

theorem pairing_apply (n : ℕ) (y : (P n).W') (x : (P n).W) :
    (P n).pairingEquiv y x = y.val.1 (WCoordinates n x) := by
  rw [(P n).pairingEquiv_apply, TauCeti.polar_splitEvenForm, W_fst]
  simp only [LinearMap.zero_apply, zero_add]
  rfl

theorem dualAction_fst {n : ℕ} (g : SpecialUnitaryRealification.Source n) (y : (P n).W') :
    (PolarizedExteriorAction.dualAction (P n) (WAction g) y).val.1 =
      y.val.1.comp (SpecialUnitaryRealification.complexAction g).symm.toLinearMap := by
  apply LinearMap.ext
  intro z
  have h := DFunLike.congr_fun
    (PolarizedExteriorAction.dualAction_pairing (P n) (WAction g) y) ((WCoordinates n).symm z)
  simp only [pairing_apply, LinearMap.comp_apply, LinearEquiv.apply_symm_apply] at h
  simpa [WAction, WCoordinates] using h

theorem vectorAction_formula {n : ℕ} (g : SpecialUnitaryRealification.Source n)
    (v : TauCeti.SplitEvenSpace ℂ n) :
    PolarizedExteriorAction.vectorAction (P n) (WAction g) v =
      (v.1.comp (SpecialUnitaryRealification.complexAction g).symm.toLinearMap,
        SpecialUnitaryRealification.complexAction g v.2) := by
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := (P n).decompositionEquiv.surjective v
  have hz : (z : TauCeti.SplitEvenSpace ℂ n) = 0 :=
    Submodule.mem_bot ℂ |>.mp ((TauCeti.splitEvenPolarization_line ℂ n) ▸ z.property)
  rw [(P n).decompositionEquiv_apply, hz, add_zero, map_add,
    PolarizedExteriorAction.vectorAction_W, PolarizedExteriorAction.vectorAction_W']
  apply Prod.ext
  · simp only [Prod.fst_add, W_fst, zero_add, dualAction_fst]
  · simp only [Prod.snd_add, W'_snd, add_zero]
    rfl

theorem coordinates_snd (n : ℕ) (v : RealSpace n) :
    (coordinates n v).2 = SpecialUnitaryRealification.coordinates n v := by
  funext i
  apply Complex.ext <;> simp [coordinates, complexCoordinates, SpecialUnitaryRealification.coordinates]

theorem coordinates_fst (n : ℕ) (v : RealSpace n) (z : Fin n → ℂ) :
    (coordinates n v).1 z = star (SpecialUnitaryRealification.coordinates n v) ⬝ᵥ z := by
  change (∑ i, ((v (Fin.castAdd n i) : ℂ) + -Complex.I * (v (Fin.natAdd n i) : ℂ)) * z i) = _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Complex.ext <;> simp [SpecialUnitaryRealification.coordinates]

theorem coordinates_naturality {n : ℕ} (g : SpecialUnitaryRealification.Source n)
    (v : RealSpace n) :
    PolarizedExteriorAction.vectorAction (P n) (WAction g) (coordinates n v) =
      coordinates n (SpecialUnitaryRealification.realAction g v) := by
  rw [vectorAction_formula]
  apply Prod.ext
  · apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := (SpecialUnitaryRealification.complexAction g).surjective z
    change (coordinates n v).1 ((SpecialUnitaryRealification.complexAction g).symm
      (SpecialUnitaryRealification.complexAction g w)) =
        (coordinates n (SpecialUnitaryRealification.realAction g v)).1
          (SpecialUnitaryRealification.complexAction g w)
    rw [LinearEquiv.symm_apply_apply]
    simp only [coordinates_fst,
      SpecialUnitaryRealification.coordinates_realAction, SpecialUnitaryRealification.complexAction_apply,
      Matrix.star_mulVec]
    have hu : g.val.conjTranspose * g.val = 1 := g.property.1.1
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  · simp only [coordinates_snd, SpecialUnitaryRealification.coordinates_realAction]

def exteriorAction {n : ℕ} (g : SpecialUnitaryRealification.Source n) :
    Fock.Space n ≃ₗ[ℂ] Fock.Space n := (ExteriorNaturality.mapEquiv (WAction g)).toLinearEquiv

theorem generator_naturality {n : ℕ} (g : SpecialUnitaryRealification.Source n)
    (v : RealSpace n) (s : Fock.Space n) :
    exteriorAction g (Fock.generator n v s) =
      Fock.generator n (SpecialUnitaryRealification.realAction g v) (exteriorAction g s) := by
  have h := PolarizedExteriorAction.cliffordOperator_naturality (P n)
    (TauCeti.splitEvenPolarization_line ℂ n) (WAction g) (coordinates n v) s
  rw [coordinates_naturality] at h
  simpa only [exteriorAction, P, AlgEquiv.toLinearEquiv_apply,
    Fock.generator, LinearMap.comp_apply, Fock.algebraAction,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    cliffordMap_ι, TauCeti.spinAction_ι] using h

end

end Math.CompactSpin.ExteriorComparison
