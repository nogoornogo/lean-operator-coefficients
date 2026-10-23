import Physics.StandardModel.Operators.Dipole.S3DipoleSelection
import Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalExteriorCompleteness
import TauCeti.RepresentationTheory.Symmetric.SignCharacter
import Math.LinearAlgebra.Selection.SelectionCriteria
import Math.RepresentationTheory.Content.FiniteFlavorControls
import Math.RepresentationTheory.Decomposition.CommonIrreducible
import Mathlib.RepresentationTheory.Maschke

/-! Unequal S3 actions on three-dimensional SM flavor carriers. -/
namespace Physics.S3QqueTensorSamples
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria
open scoped TensorProduct BigOperators
abbrev H := S3DipoleSelection.H
abbrev V := S3DipoleSelection.V
abbrev q := S3DipoleSelection.action
abbrev trivial : Representation ℂ H V := Representation.trivial ℂ H V
def signCharacter := TauCeti.signLinearCharacter ℂ (Fin 3)
def sign : Representation ℂ H V where
  toFun g := (signCharacter g : ℂ) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; funext i; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    funext i
    simp [map_mul, smul_smul, mul_comm]

@[simp] theorem sign_apply (g : H) (x : V) (i : Fin 3) :
    sign g x i = (signCharacter g : ℂ) * x i := rfl

theorem sign_swap (a b : Fin 3) (hab : a ≠ b) (x : V) :
    sign (Equiv.swap a b) x = -x := by
  ext i
  simp [sign_apply, signCharacter, TauCeti.signLinearCharacter_swap hab]

def unit (i : Fin 3) : V := Pi.single i 1

@[simp] theorem q_unit (g : H) (i : Fin 3) : q g (unit i) = unit (g i) :=
  S3DipoleSelection.action_single g i

abbrev Residual := QquePhysicalOrderedCompleteness.Residual q trivial sign
abbrev SymmetricResidual := QquePhysicalExteriorCompleteness.residualSpace q trivial sign
def entry (f : SymmetricResidual) (i j a b : Fin 3) : ℂ :=
  f.val ((unit i ⊗ₜ[ℂ] unit j) ⊗ₜ[ℂ]
    (unit a ⊗ₜ[ℂ] unit b))

theorem entry_symmetric (f : SymmetricResidual) (i j a b : Fin 3) :
    entry f j i a b = entry f i j a b := f.property _ _ _ _

theorem entry_swap (f : SymmetricResidual) (s t : Fin 3) (hst : s ≠ t)
    (i j a b : Fin 3) :
    entry f (Equiv.swap s t i) (Equiv.swap s t j) a b = -entry f i j a b := by
  have he := IntertwiningMap.isIntertwining _ _ f.val (Equiv.swap s t)
    ((unit i ⊗ₜ[ℂ] unit j) ⊗ₜ[ℂ]
      (unit a ⊗ₜ[ℂ] unit b))
  simp only [Representation.tprod_apply, TensorProduct.map_tmul,
    q_unit, sign_swap s t hst,
    Representation.trivial_apply, TensorProduct.tmul_neg] at he
  change f.val.toLinearMap (-((unit (Equiv.swap s t i) ⊗ₜ[ℂ]
    unit (Equiv.swap s t j)) ⊗ₜ[ℂ] (unit a ⊗ₜ[ℂ] unit b))) =
    f.val.toLinearMap ((unit i ⊗ₜ[ℂ] unit j) ⊗ₜ[ℂ]
      (unit a ⊗ₜ[ℂ] unit b)) at he
  have hn := (map_neg f.val.toLinearMap
    ((unit (Equiv.swap s t i) ⊗ₜ[ℂ] unit (Equiv.swap s t j)) ⊗ₜ[ℂ]
      (unit a ⊗ₜ[ℂ] unit b))).symm.trans he
  change -entry f (Equiv.swap s t i) (Equiv.swap s t j) a b = entry f i j a b at hn
  exact neg_eq_iff_eq_neg.mp hn

@[simp] theorem fin_one (h : 1 < 3) : (⟨1,h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := rfl

theorem entry_zero (f : SymmetricResidual) (i j a b : Fin 3) : entry f i j a b = 0 := by
  have h01 := entry_swap f 0 1 (by decide) i j a b
  have h02 := entry_swap f 0 2 (by decide) i j a b
  have h12 := entry_swap f 1 2 (by decide) i j a b
  have hs := entry_symmetric f i j a b
  fin_cases i <;> fin_cases j <;>
    norm_num [Equiv.swap_apply_def, Fin.ext_iff] at h01 h02 h12
  all_goals simp only [Fin.mk_zero, fin_one, fin_two] at *
  all_goals first
    | (linear_combination (1/2 : ℂ) * h01)
    | (linear_combination (1/2 : ℂ) * h02)
    | (linear_combination (1/2 : ℂ) * h12)
    | (linear_combination (1/2 : ℂ) * h01 - (1/2 : ℂ) * hs)
    | (linear_combination (1/2 : ℂ) * h02 - (1/2 : ℂ) * hs)
    | (linear_combination (1/2 : ℂ) * h12 - (1/2 : ℂ) * hs)

theorem basis_expansion (x : V) : x = ∑ i, x i • unit i := by
  ext j
  simp [unit, Pi.single_apply]

theorem residual_zero (f : SymmetricResidual) : f = 0 := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i x y z r
  have hz : ∀ i j a b : Fin 3, f.val.toLinearMap
      ((unit i ⊗ₜ[ℂ] unit j) ⊗ₜ[ℂ]
        (unit a ⊗ₜ[ℂ] unit b)) = 0 := entry_zero f
  rw [basis_expansion x, basis_expansion y, basis_expansion z, basis_expansion r]
  simp [hz]

theorem forbidden_permutation_trivial_sign :
    Forbidden (QquePhysicalExteriorCompleteness.Sector q trivial sign) := by
  rw [(ofEquiv (QquePhysicalExteriorCompleteness.exteriorEquiv q trivial sign)).forbidden]
  exact residual_zero

def pairSum : (V ⊗[ℂ] V) →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂
    (FiniteFlavorControls.coordinateSum 3) (FiniteFlavorControls.coordinateSum 3))

@[simp] theorem pairSum_tmul (x y : V) :
    pairSum (x ⊗ₜ[ℂ] y) = (∑ i, x i) * (∑ i, y i) := rfl

theorem sign_square (g : H) : (signCharacter g : ℂ) * (signCharacter g : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;>
    simp [signCharacter, TauCeti.coe_signLinearCharacter_apply, h]

def positiveCoefficient : QquePhysicalOrderedCompleteness.Residual q sign sign where
  toLinearMap := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ pairSum pairSum)
  isIntertwining' g := by
    repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
    rename_i x y z r
    change pairSum (q g x ⊗ₜ[ℂ] q g y) * pairSum (sign g z ⊗ₜ[ℂ] sign g r) =
      pairSum (x ⊗ₜ[ℂ] y) * pairSum (z ⊗ₜ[ℂ] r)
    simp only [pairSum_tmul, S3DipoleSelection.action_apply, sign_apply, ← Finset.mul_sum]
    rw [Equiv.sum_comp g⁻¹ x, Equiv.sum_comp g⁻¹ y]
    have hs := sign_square g
    calc
      _ = ((∑ i, x i) * (∑ i, y i)) *
          (((signCharacter g : ℂ) * (signCharacter g : ℂ)) *
            ((∑ i, z i) * (∑ i, r i))) := by ring
      _ = _ := by rw [hs]; ring

def positiveResidual : QquePhysicalExteriorCompleteness.residualSpace q sign sign :=
  ⟨positiveCoefficient, by
    intro x y z r
    change pairSum (y ⊗ₜ[ℂ] x) * pairSum (z ⊗ₜ[ℂ] r) =
      pairSum (x ⊗ₜ[ℂ] y) * pairSum (z ⊗ₜ[ℂ] r)
    simp only [pairSum_tmul]
    ring⟩

theorem positive_witness :
    positiveResidual.val ((unit 0 ⊗ₜ[ℂ] unit 0) ⊗ₜ[ℂ] (unit 0 ⊗ₜ[ℂ] unit 0)) = 1 := by
  change pairSum (unit 0 ⊗ₜ[ℂ] unit 0) * pairSum (unit 0 ⊗ₜ[ℂ] unit 0) = 1
  simp [unit, pairSum_tmul, Pi.single_apply]

theorem positive_nonzero : positiveResidual ≠ 0 := by
  intro hz
  have he := positive_witness
  rw [hz] at he
  norm_num at he

theorem allowed_permutation_sign_sign :
    Allowed (QquePhysicalExteriorCompleteness.Sector q sign sign) := by
  rw [(ofEquiv (QquePhysicalExteriorCompleteness.exteriorEquiv q sign sign)).allowed]
  exact ⟨positiveResidual, positive_nonzero⟩

theorem intertwiner_entry_zero (f : IntertwiningMap q sign) (i a : Fin 3) :
    f (unit i) a = 0 := by
  have hh (s t : Fin 3) (hst : s ≠ t) :
      f (unit (Equiv.swap s t i)) a = -f (unit i) a := by
    have he := IntertwiningMap.isIntertwining _ _ f (Equiv.swap s t) (unit i)
    rw [q_unit, sign_swap s t hst] at he
    exact congrArg (fun v : V => v a) he
  have h01 := hh 0 1 (by decide)
  have h02 := hh 0 2 (by decide)
  have h12 := hh 1 2 (by decide)
  fin_cases i <;> norm_num [Equiv.swap_apply_def, Fin.ext_iff] at h01 h02 h12
  all_goals simp only [Fin.mk_zero, fin_one, fin_two] at *
  all_goals first
    | linear_combination (1/2 : ℂ) * h01
    | linear_combination (1/2 : ℂ) * h02
    | linear_combination (1/2 : ℂ) * h12

theorem no_q_to_sign (f : IntertwiningMap q sign) : f = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  ext a
  rw [basis_expansion x]
  simp [intertwiner_entry_zero]

theorem no_shared_q_sign : ¬ CommonIrreducible.Shares q sign := by
  have hc : Nat.card H = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let : NeZero (Nat.card H : ℂ) := ⟨by rw [hc]; norm_num⟩
  exact (CommonIrreducible.all_zero_iff q sign (by infer_instance)).mp no_q_to_sign

/-- Under a neutral-Higgs flavor-map interpretation this cannot supply
three full-rank quark masses; this statement concerns the actual map. -/
theorem q_to_trivial_not_injective (f : IntertwiningMap q trivial) :
    ¬ Function.Injective f := by
  intro hi
  have he := IntertwiningMap.isIntertwining _ _ f (Equiv.swap (0 : Fin 3) 1) (unit 0)
  have hs : q (Equiv.swap (0 : Fin 3) 1) (unit 0) = unit 1 := by simp
  rw [hs] at he
  have hu := hi he
  have hc := congrArg (fun v : V => v 0) hu
  norm_num [unit, Pi.single_apply] at hc

theorem no_q_trivial_equiv (e : Representation.Equiv q trivial) : False :=
  q_to_trivial_not_injective e.toIntertwiningMap e.toLinearEquiv.injective

theorem no_q_sign_equiv (e : Representation.Equiv q sign) : False := by
  have hz := no_q_to_sign e.toIntertwiningMap
  have he := congrArg (fun f : IntertwiningMap q sign => f (unit 0)) hz
  have hu := e.toLinearEquiv.injective (he.trans (map_zero e.toLinearEquiv).symm)
  have hc := congrArg (fun v : V => v 0) hu
  norm_num [unit, Pi.single_apply] at hc

/-- The species dictionary cannot arise from one common multiplicity
representation by equivariant identifications of both species. -/
theorem no_uniform_flavor_dictionary {W : Type*} [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ H W) (eqQ : Representation.Equiv a q) :
    (∀ _eqU : Representation.Equiv a trivial, False) ∧
      (∀ _eqU : Representation.Equiv a sign, False) :=
  ⟨fun eqU => no_q_trivial_equiv (eqQ.symm.trans eqU),
    fun eqU => no_q_sign_equiv (eqQ.symm.trans eqU)⟩

/-- The independent flavor actions really preserve the actual SM action. -/
theorem independent_flavor_preserves_sm {X : Type*} [AddCommGroup X] [Module ℂ X]
    (r : Representation ℂ StandardSMGaugeTensor.GaugeGroup X)
    (a : Representation ℂ H V) (g : StandardSMGaugeTensor.GaugeGroup) (h : H) :
    Commute ((ExternalInvariantTensor.external r a) (g,1))
      ((ExternalInvariantTensor.external r a) (1,h)) := by
  change (ExternalInvariantTensor.external r a) (g,1) *
      (ExternalInvariantTensor.external r a) (1,h) =
    (ExternalInvariantTensor.external r a) (1,h) *
      (ExternalInvariantTensor.external r a) (g,1)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

end
end Physics.S3QqueTensorSamples
