import Math.RepresentationTheory.TensorPowerDualEquivalence
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! A determinant-one volume gives an actual split unit in a tensor power.
The alternating section is normalized symbolically by the factorial. -/
namespace Math.TensorVolumeSplit
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (rho : Representation ℂ G V) (b : Module.Basis (Fin n) ℂ V)
  (hd : ∀ g, LinearMap.det (rho g) = 1)

@[reducible] local instance (m : ℕ) : AddCommGroup (⨂[ℂ]^m V) := inferInstance

def topEquivalence : Representation.Equiv (rho.exteriorPower n) (trivial ℂ G ℂ) where
  toLinearEquiv := exteriorPower.topEquiv b
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change exteriorPower.topEquiv b (exteriorPower.map n (rho g) x) = exteriorPower.topEquiv b x
    rw [exteriorPower.map_top_eq_det_smul b,hd g,one_smul]
    rfl

def projection : IntertwiningMap (rho.tensorPower n) (rho.exteriorPower n) where
  toLinearMap := exteriorPower.fromTensorPower ℂ V n
  isIntertwining' g := by
    exact (exteriorPower.map_comp_fromTensorPower n (rho g)).symm

def alternation : IntertwiningMap (rho.exteriorPower n) (rho.tensorPower n) where
  toLinearMap := (n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ V n
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change (n.factorial : ℂ)⁻¹ •
      exteriorPower.toTensorPower ℂ V n (exteriorPower.map n (rho g) x) =
      (rho.tensorPower n) g ((n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ V n x)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (exteriorPower.toTensorPower_comp_map n (rho g)) x

theorem projection_alternation (x : ⋀[ℂ]^n V) :
    projection rho (alternation rho x) = x := by
  change exteriorPower.fromTensorPower ℂ V n
    ((n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ V n x) = x
  rw [map_smul]
  have he := LinearMap.congr_fun
    (exteriorPower.fromTensorPower_comp_toTensorPower (R := ℂ) (M := V) n) x
  change exteriorPower.fromTensorPower ℂ V n (exteriorPower.toTensorPower ℂ V n x) =
    n.factorial • x at he
  rw [he,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),one_smul]

def coefficient : IntertwiningMap (rho.tensorPower n) (trivial ℂ G ℂ) :=
  (topEquivalence rho b hd).toIntertwiningMap.comp (projection rho)

def sectionMap : IntertwiningMap (trivial ℂ G ℂ) (rho.tensorPower n) :=
  (alternation rho).comp (topEquivalence rho b hd).symm.toIntertwiningMap

theorem retraction (z : ℂ) : coefficient rho b hd (sectionMap rho b hd z) = z := by
  change topEquivalence rho b hd
    (projection rho (alternation rho ((topEquivalence rho b hd).symm z))) = z
  rw [projection_alternation,Representation.Equiv.apply_symm_apply]

theorem coefficient_tprod (v : Fin n → V) :
    coefficient rho b hd (PiTensorProduct.tprod ℂ v) = b.det v := by
  change exteriorPower.topEquiv b
    (exteriorPower.fromTensorPower ℂ V n (PiTensorProduct.tprod ℂ v)) = _
  rw [exteriorPower.fromTensorPower_tprod,exteriorPower.topEquiv_apply_ιMulti]

def split : SplitRepresentationProjection.Split (rho.tensorPower n) (trivial ℂ G ℂ) where
  project := coefficient rho b hd
  embed := sectionMap rho b hd
  left_inv := retraction rho b hd

def zeroEquivalence : Representation.Equiv (rho.tensorPower 0) (trivial ℂ G ℂ) where
  toLinearEquiv := PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℂ) (s := fun _ => V)
  isIntertwining' g := by
    rw [Representation.tensorPower_zero_apply]
    rfl

def add {p q : ℕ}
    (S : SplitRepresentationProjection.Split (rho.tensorPower p) (trivial ℂ G ℂ))
    (T : SplitRepresentationProjection.Split (rho.tensorPower q) (trivial ℂ G ℂ)) :
    SplitRepresentationProjection.Split (rho.tensorPower (p+q)) (trivial ℂ G ℂ) :=
  ((SplitRepresentationProjection.Split.ofEquiv (rho.tensorPowerAddEquiv p q).symm).trans
    (S.tensor T)).trans
      (SplitRepresentationProjection.Split.ofEquiv
        (Representation.TensorProduct.lid ℂ (trivial ℂ G ℂ)))

def powerCast {p q : ℕ} (he : p=q) : Representation.Equiv (rho.tensorPower p) (rho.tensorPower q) where
  toLinearEquiv := _root_.TensorPower.cast ℂ V he
  isIntertwining' g := by
    subst q
    simp only [_root_.TensorPower.cast_refl]
    rfl

theorem powerCast_tprod {p q : ℕ} (he : p=q) (v : Fin p → V) :
    powerCast rho he (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (v ∘ Fin.cast he.symm) := _root_.TensorPower.cast_tprod ℂ V he v

def multiple : (k : ℕ) →
    SplitRepresentationProjection.Split (rho.tensorPower (n*k)) (trivial ℂ G ℂ)
  | 0 => SplitRepresentationProjection.Split.ofEquiv (zeroEquivalence rho)
  | k+1 => (SplitRepresentationProjection.Split.ofEquiv (powerCast rho (Nat.mul_succ n k))).trans
      (add rho (multiple k) (split rho b hd))

/-- Appending determinant volumes supplies the retraction needed to balance
an arbitrary mixed coefficient. -/
def raiseDegree (q k : ℕ) : SplitRepresentationProjection.Split
    (rho.tensorPower (q+n*k)) (rho.tensorPower q) :=
  ((SplitRepresentationProjection.Split.ofEquiv (rho.tensorPowerAddEquiv q (n*k)).symm).trans
    ((SplitRepresentationProjection.Split.ofEquiv (.refl (rho.tensorPower q))).tensor
      (multiple rho b hd k))).trans
        (SplitRepresentationProjection.Split.ofEquiv
          (Representation.TensorProduct.rid ℂ (rho.tensorPower q)))

theorem raiseDegree_project (q k : ℕ) (x : ⨂[ℂ]^q V) (y : ⨂[ℂ]^(n*k) V) :
    (raiseDegree rho b hd q k).project (rho.tensorPowerAddEquiv q (n*k) (x ⊗ₜ[ℂ] y)) =
      (multiple rho b hd k).project y • x := by
  change Representation.TensorProduct.rid ℂ (rho.tensorPower q)
    (((IntertwiningMap.id (rho.tensorPower q)).tensor (multiple rho b hd k).project)
      ((rho.tensorPowerAddEquiv q (n*k)).symm
        (rho.tensorPowerAddEquiv q (n*k) (x ⊗ₜ[ℂ] y)))) = _
  rw [Representation.Equiv.symm_apply_apply]
  rfl

end
end Math.TensorVolumeSplit
