import GUT.SU5.Matching.TreeMatching
import Physics.StandardModel.Operators.MediatorQque

open Math

/-! The SU(5) pilot as an application of the general inverse-mass API.
The original action, currents, mass assumptions and normalization are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU5.MediatorMatching
noncomputable section
open SMEpsilonTensor StandardSMGaugeTensor HeavyCurrents
open scoped TensorProduct

abbrev Channels := Fin 3 → Fin 2 → ℂ

def pairing : Channels →ₗ[ℂ] Module.Dual ℂ Channels :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i : Fin 3, ∑ w : Fin 2, x i w * y i w)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum, mul_add])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum, mul_add])

def leftCurrent : Quark ⊗[ℂ] Color →ₗ[ℂ] Channels :=
  LinearMap.pi fun i => LinearMap.pi fun w => TensorProduct.lift (upCurrent i w)

def rightCurrent : Quark ⊗[ℂ] ℂ →ₗ[ℂ] Module.Dual ℂ Channels :=
  pairing.comp (LinearMap.pi fun i => LinearMap.pi fun w =>
    TensorProduct.lift (electronCurrent i w))

theorem current_pair (q r : Quark) (u : Color) (e : ℂ) :
    rightCurrent (r ⊗ₜ[ℂ] e) (leftCurrent (q ⊗ₜ[ℂ] u)) = contraction q r u e := by
  change (∑ i : Fin 3, ∑ w : Fin 2, electronCurrent i w r e * upCurrent i w q u) = _
  simp only [contraction, mul_comm]

def mass (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : Channels ≃ₗ[ℂ] Channels :=
  MediatorExchange.scalarMass (AdjointMass.massSquared g v : ℂ)
    (AdjointMass.massSquared_ne_zero hg hv)

def coefficient (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : QQueSpace →ₗ[ℂ] ℂ :=
  MediatorExchange.coefficient (mass g v hg hv) (g : ℂ) leftCurrent rightCurrent

theorem coefficient_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    coefficient g v hg hv = TreeMatching.orderedWilson g v • qque := by
  apply TensorProduct.ext_fourfold'
  intro q r u e
  rw [coefficient, MediatorExchange.coefficient_tmul]
  simp only [mass, MediatorExchange.scalarMass_symm_apply, map_smul, smul_eq_mul,
    current_pair, contraction_eq_qque]
  change -(g : ℂ) ^ 2 * ((AdjointMass.massSquared g v : ℂ)⁻¹ * qque _) =
    TreeMatching.orderedWilson g v * qque _
  simp only [TreeMatching.orderedWilson, div_eq_mul_inv]
  ring

theorem invariant (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorQque.IsInvariant quark upRight electronRight (mass g v hg hv)
      (g : ℂ) leftCurrent rightCurrent := by
  intro a z
  change coefficient g v hg hv _ = coefficient g v hg hv _
  rw [coefficient_eq]
  exact congrArg (fun f => f z) ((TreeMatching.matchedInternal g v).isIntertwining' a)

def generated (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :=
  MediatorQque.sector quark upRight electronRight (mass g v hg hv)
    (g : ℂ) leftCurrent rightCurrent (invariant g v hg hv)

theorem internal_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    MediatorQque.internal quark upRight electronRight (mass g v hg hv)
      (g : ℂ) leftCurrent rightCurrent (invariant g v hg hv) =
      TreeMatching.matchedInternal g v := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun (coefficient_eq g v hg hv) z

theorem generated_eq (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    (generated g v hg hv).val = TreeMatching.matchedExterior g v := by
  change QqueSpinorExterior.exterior _ _ _ _ = _
  rw [internal_eq]
  rfl

theorem generated_nonzero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    generated g v hg hv ≠ 0 := by
  intro h
  have hz := congrArg Subtype.val h
  rw [generated_eq] at hz
  exact TreeMatching.matchedExterior_nonzero hg hv hz

theorem ordered_eq_original_action (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (q r : Quark) (u : Color) (e : ℂ) (s t z l : WeylSpinor.Space) :
    QqueSpinorExterior.ordered quark upRight electronRight
      (MediatorQque.internal quark upRight electronRight (mass g v hg hv)
        (g : ℂ) leftCurrent rightCurrent (invariant g v hg hv))
      (((q ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (r ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
        ((u ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] l))) =
      TreeMatching.eliminated g v q r u e s t z l := by
  rw [internal_eq]
  exact TreeMatching.matchedOrdered_eq_eliminated g v hg hv q r u e s t z l

end
end GUT.SU5.MediatorMatching
