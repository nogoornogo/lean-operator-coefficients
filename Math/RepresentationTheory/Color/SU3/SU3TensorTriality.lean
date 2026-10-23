import Math.RepresentationTheory.Color.SU3.SU3TensorPositive
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Necessary and sufficient positive scalar coupling for arbitrary defining
and dual SU3 tensor powers. Triality is sufficient here because the tensor
powers are unrestricted; no such sufficiency is asserted for Schur summands. -/
namespace Math.SU3TensorTriality
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior SU3TensorPositive InvariantCoefficientProduct
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance

def center (z : Circle) (hz : z^3=1) : Group :=
  ⟨Matrix.diagonal (fun _ => (z : ℂ)),by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i=j
      · subst j
        simp [← Circle.coe_inv_eq_conj,z.coe_ne_zero]
      · simp [h]
    · rw [Matrix.det_diagonal]
      have hp : (z : ℂ)^3=1 := congrArg (fun t : Circle => (t : ℂ)) hz
      simpa [Fin.prod_univ_succ,pow_succ] using hp⟩

theorem defining_center (z : Circle) (hz : z^3=1) (v : Vector) :
    rho (center z hz) v=(z : ℂ) • v := by
  ext i
  simp [rho,SmallSpecialUnitary.defining,center,Matrix.toLin'_apply,Matrix.mulVec]

theorem dual_scalar {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ G V) (g : G) (c : ℂ) (hc : c≠0)
    (h : ∀ v, r g v=c • v) (phi : Module.Dual ℂ V) : r.dual g phi=c⁻¹ • phi := by
  have hi (v : V) : r g⁻¹ v=c⁻¹ • v := by
    have he : r g (r g⁻¹ v)=v := Representation.self_inv_apply r g v
    rw [h] at he
    simpa [smul_smul,hc] using congrArg (fun x => c⁻¹ • x) he
  ext v
  change phi (r g⁻¹ v)=c⁻¹*phi v
  rw [hi,map_smul,smul_eq_mul]

theorem power_scalar {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ G V) (g : G) (c : ℂ) (h : ∀ v, r g v=c • v)
    (n : ℕ) (x : ⨂[ℂ]^n V) : r.tensorPower n g x=c^n • x := by
  have he : r.tensorPower n g=c^n • LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,Representation.tensorPower_apply,
      PiTensorProduct.map_tprod,LinearMap.smul_apply,LinearMap.id_apply]
    change PiTensorProduct.tprod ℂ (fun i => r g (v i))=c^n • PiTensorProduct.tprod ℂ v
    simp only [h]
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
    simp
  exact LinearMap.congr_fun he x

theorem mixed_center (z : Circle) (hz : z^3=1) (a b : ℕ)
    (x : (⨂[ℂ]^a Vector) ⊗[ℂ] (⨂[ℂ]^b (Module.Dual ℂ Vector))) :
    mixed a b (center z hz) x=((z : ℂ)^a*((z : ℂ)⁻¹)^b) • x := by
  have he : mixed a b (center z hz)=((z : ℂ)^a*((z : ℂ)⁻¹)^b) • LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    change rho.tensorPower a (center z hz) x ⊗ₜ[ℂ] rho.dual.tensorPower b (center z hz) y=_
    rw [power_scalar rho _ _ (defining_center z hz),
      power_scalar rho.dual _ _ (dual_scalar rho _ _ z.coe_ne_zero (defining_center z hz))]
    exact TensorProduct.smul_tmul_smul _ _ _ _
  exact LinearMap.congr_fun he x

def root : Circle := Circle.exp (2*Real.pi/3)

theorem root_primitive : IsPrimitiveRoot (root : ℂ) 3 := by
  have he : (root : ℂ)=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [root,Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp 3 (by decide)

theorem root_cube : root^3=1 := by
  apply Subtype.coe_injective
  exact root_primitive.pow_eq_one

/-- Exclusion by the actual scalar center, not by a necessary condition
mistakenly asserted sufficient for restricted color branches. -/
theorem necessary (a b : ℕ)
    (ha : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (mixed a b))) :
    a%3=b%3 := by
  obtain ⟨f,x,hx⟩ := (hasUnit_iff (mixed a b)).mpr ha
  have he := f.isIntertwining _ _ (center root root_cube) x
  change f (mixed a b (center root root_cube) x)=f x at he
  rw [mixed_center,map_smul,hx,smul_eq_mul,mul_one] at he
  have hp : (root : ℂ)^a=(root : ℂ)^b := by
    have hn : (root : ℂ)^b≠0 := pow_ne_zero _ root.coe_ne_zero
    rw [inv_pow,← div_eq_mul_inv,div_eq_one_iff_eq hn] at he
    exact he
  have hm := (root_primitive.isOfFinOrder (by decide)).pow_eq_pow_iff_modEq.mp hp
  change a%orderOf (root : ℂ)=b%orderOf (root : ℂ) at hm
  simpa only [← root_primitive.eq_orderOf] using hm

/-- A closed positive coupling criterion for all unrestricted defining/dual
color tensor powers. No multiplicity, rank table or Weyl premise remains. -/
theorem allowed_iff (a b : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (mixed a b)) ↔ a%3=b%3 :=
  ⟨necessary a b,fun h => (hasUnit_iff (mixed a b)).mp (positive a b h)⟩

theorem forbidden_iff (a b : ℕ) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (mixed a b)) ↔ a%3≠b%3 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]

end
end Math.SU3TensorTriality
