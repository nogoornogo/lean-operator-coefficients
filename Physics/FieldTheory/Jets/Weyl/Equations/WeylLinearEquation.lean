import Math.Algebra.Jets.LinearJetEquation
import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP

/-! The free left-chiral Weyl equation in the existing source-vector convention.
Its equation parameters carry the dual right-spin representation. -/
namespace Physics.WeylLinearEquation
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear Math.JetDirections Matrix Representation
open scoped BigOperators

abbrev Group := WeylSpinor.Group
abbrev Coordinates := LorentzDirections.Coordinates
abbrev Spinor := WeylSpinor.Space
abbrev Jets := Jet (Fin 2) (Fin 4)
abbrev Equations := Module.Dual ℂ Spinor

def contractMatrix (f : Equations) (a : LorentzDirections.Mat) : Spinor :=
  fun i => f (fun j => a i j)

def contract : Equations →ₗ[ℂ] (Coordinates →ₗ[ℂ] Spinor) where
  toFun f := {
    toFun v := contractMatrix f (LorentzDirections.pauli v)
    map_add' v w := by
      funext i
      change f (fun j => LorentzDirections.pauli (v + w) i j) = _
      simp only [map_add, Matrix.add_apply]
      exact f.map_add _ _
    map_smul' c v := by
      funext i
      change f (fun j => LorentzDirections.pauli (c • v) i j) = _
      simp only [map_smul, Matrix.smul_apply]
      exact f.map_smul c _ }
  map_add' f h := rfl
  map_smul' c f := rfl

theorem contract_matrix (g : Group) (f : Equations) (a : LorentzDirections.Mat) :
    contractMatrix f (LorentzDirections.matrixAction g a) =
      WeylSpinor.left g (contractMatrix (WeylSpinor.right.dual g⁻¹ f) a) := by
  have hf : WeylSpinor.right.dual g⁻¹ f = f.comp (WeylSpinor.right g) := by
    change f.comp (WeylSpinor.right (g⁻¹)⁻¹) = _
    rw [inv_inv]
  rw [hf]
  funext i
  change f (fun j => ((g : LorentzDirections.Mat) * a * (g : LorentzDirections.Mat)ᴴ) i j) =
    (g : LorentzDirections.Mat).mulVec (fun k => f (WeylSpinor.right g (fun j => a k j))) i
  simp_rw [WeylSpinor.right_apply]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, conjTranspose_apply,
    Fin.sum_univ_two]
  have he : (fun j =>
      ((g : LorentzDirections.Mat) i 0 * a 0 0 + (g : LorentzDirections.Mat) i 1 * a 1 0) * star ((g : LorentzDirections.Mat) j 0) +
      ((g : LorentzDirections.Mat) i 0 * a 0 1 + (g : LorentzDirections.Mat) i 1 * a 1 1) * star ((g : LorentzDirections.Mat) j 1)) =
      (g : LorentzDirections.Mat) i 0 • (fun j => star ((g : LorentzDirections.Mat) j 0) * a 0 0 + star ((g : LorentzDirections.Mat) j 1) * a 0 1) +
      (g : LorentzDirections.Mat) i 1 • (fun j => star ((g : LorentzDirections.Mat) j 0) * a 1 0 + star ((g : LorentzDirections.Mat) j 1) * a 1 1) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_smul, map_smul]
  have hh (k : Fin 2) : ((g : LorentzDirections.Mat).map star).mulVec (fun j => a k j) =
      (fun j => star ((g : LorentzDirections.Mat) j 0) * a k 0 + star ((g : LorentzDirections.Mat) j 1) * a k 1) := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  rw [hh 0, hh 1]
  rfl

theorem contract_covariant (g : Group) (f : Equations) :
    contract (WeylSpinor.right.dual g f) =
      (WeylSpinor.left g).comp ((contract f).comp (LorentzDirections.vector g⁻¹)) := by
  apply LinearMap.ext
  intro v
  have he := contract_matrix g (WeylSpinor.right.dual g f)
    (LorentzDirections.pauli (LorentzDirections.vector g⁻¹ v))
  rw [LorentzDirections.matrixAction_apply, ← LorentzDirections.pauli_vector] at he
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, inv_mul_cancel, map_one,
    Module.End.one_apply] at he
  exact he

def frame : (Coordinates →ₗ[ℂ] JetLinear.Field (Fin 2)) →ₗ[ℂ] Jets where
  toFun a := ∑ i : Fin 4, JetLinear.shift i (atOrder 0 (a (Pi.single i 1)))
  map_add' a b := by simp only [LinearMap.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c a := by simp only [LinearMap.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem expand (v : Coordinates) : v = ∑ i : Fin 4, v i • Pi.single i (1 : ℂ) := by
  ext i
  simp [Pi.single_apply]

theorem frame_covariant (g : Group) (a : Coordinates →ₗ[ℂ] JetLinear.Field (Fin 2)) :
    combined (LorentzJetIBP.weyl false) LorentzDirections.direction g (frame a) =
      frame ((LorentzJetIBP.weyl false g).comp (a.comp (LorentzDirections.vector g⁻¹))) := by
  simp only [frame, LinearMap.coe_mk, AddHom.coe_mk, map_sum, combined_covariant, combined_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LinearMap.comp_apply]
  let k := (JetLinear.shift j).comp ((atOrder 0).comp ((LorentzJetIBP.weyl false g).comp a))
  change (∑ i : Fin 4, (LorentzDirections.direction g (Finsupp.single i 1)) j • k (Pi.single i 1)) =
    k (LorentzDirections.vector g⁻¹ (Pi.single j 1))
  rw [expand (LorentzDirections.vector g⁻¹ (Pi.single j 1)), map_sum]
  simp only [map_smul, LorentzDirections.direction_single]

def seed : Equations →ₗ[ℂ] Jets := frame.comp
  ((LinearMap.compRight ℂ (LorentzJetIBP.spinorBasis.symm.toLinearMap)).comp contract)

theorem seed_covariant (g : Group) (f : Equations) :
    combined (LorentzJetIBP.weyl false) LorentzDirections.direction g (seed f) =
      seed (WeylSpinor.right.dual g f) := by
  change combined (LorentzJetIBP.weyl false) LorentzDirections.direction g
    (frame (LorentzJetIBP.spinorBasis.symm.toLinearMap.comp (contract f))) = _
  rw [frame_covariant]
  change frame _ = frame (LorentzJetIBP.spinorBasis.symm.toLinearMap.comp (contract (WeylSpinor.right.dual g f)))
  rw [contract_covariant]
  apply congrArg frame
  apply LinearMap.ext
  intro v
  apply LorentzJetIBP.spinorBasis.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LorentzJetIBP.weyl_basis]
  simp

abbrev relations := LinearJetEquation.relations seed
abbrev Generator := LinearJetEquation.Generator seed
def action := LinearJetEquation.action seed WeylSpinor.right.dual
  (LorentzJetIBP.weyl false) LorentzDirections.direction seed_covariant

theorem descendant_zero (p : Symbols (Fin 4)) (f : Equations) :
    relations.mkQ (LinearJetEquation.multiple p (seed f)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LinearJetEquation.descendant_mem seed p f)

end
end Physics.WeylLinearEquation
