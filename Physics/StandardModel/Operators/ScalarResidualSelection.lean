import Physics.StandardModel.Operators.ResidualSelectionCriteria
import Physics.StandardModel.Operators.QqqlScalarFlavor

open Math

/-! One-generation character tests for the actual four-family residual spaces.
The charges belong to physical right-handed carriers, not their conjugates. -/
namespace GUT.ScalarResidualSelection
set_option autoImplicit false
noncomputable section
open Representation SelectionCriteria
open scoped TensorProduct
variable {H : Type*} [Group H]

abbrev Four (a b c d : Representation ℂ H ℂ) :=
  IntertwiningMap ((a.tprod b).tprod (c.tprod d)) (Representation.trivial ℂ H ℂ)

def Neutral (a b c d : Representation ℂ H ℂ) : Prop :=
  ∀ g, (a g 1 * b g 1) * (c g 1 * d g 1) = 1

theorem scalar_formula {a b c d : Representation ℂ H ℂ} (f : Four a b c d)
    (x y z w : ℂ) : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) =
      ((x*y)*(z*w)) * f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) := by
  calc
    _ = f (((x • (1 : ℂ)) ⊗ₜ[ℂ] (y • (1 : ℂ))) ⊗ₜ[ℂ]
      ((z • (1 : ℂ)) ⊗ₜ[ℂ] (w • (1 : ℂ)))) := by simp
    _ = _ := by
      rw [TensorProduct.smul_tmul_smul, TensorProduct.smul_tmul_smul,
        TensorProduct.smul_tmul_smul, map_smul]
      rfl

def coefficient (a b c d : Representation ℂ H ℂ) (h : Neutral a b c d) :
    Four a b c d where
  toLinearMap := (TensorProduct.lift (LinearMap.mul ℂ ℂ)).comp
    (TensorProduct.map (TensorProduct.lift (LinearMap.mul ℂ ℂ))
      (TensorProduct.lift (LinearMap.mul ℂ ℂ)))
  isIntertwining' g := by
    ext
    change (a g 1 * b g 1) * (c g 1 * d g 1) = (1*1)*(1*1)
    simpa only [mul_one] using h g

theorem allowed_four (a b c d : Representation ℂ H ℂ) :
    Allowed (Four a b c d) ↔ Neutral a b c d := by
  constructor
  · rintro ⟨f, hf⟩ g
    have hn : f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) ≠ 0 := by
      intro hz
      apply hf
      apply IntertwiningMap.ext
      ext
      exact hz
    have hi := IntertwiningMap.isIntertwining _ _ f g
      (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
    change f ((a g 1 ⊗ₜ[ℂ] b g 1) ⊗ₜ[ℂ] (c g 1 ⊗ₜ[ℂ] d g 1)) = f _ at hi
    rw [scalar_formula] at hi
    exact mul_right_cancel₀ hn (hi.trans (one_mul _).symm)
  · intro h
    refine ⟨coefficient a b c d h, ?_⟩
    intro hz
    have he := DFunLike.congr_fun hz
      (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
    norm_num [coefficient] at he

theorem allowed_qque (q u e : Representation ℂ H ℂ) :
    Allowed (QquePhysicalExteriorCompleteness.residualSpace q u e) ↔ Neutral q q u e := by
  constructor
  · rintro ⟨k, hk⟩
    exact (allowed_four q q u e).mp ⟨k.val, fun h => hk (Subtype.ext h)⟩
  · intro h
    refine ⟨⟨coefficient q q u e h, ?_⟩, ?_⟩
    · intro x y z w
      change ((y*x)*(z*w)) = ((x*y)*(z*w))
      ring
    · intro hz
      have he := congrArg (fun k : QquePhysicalExteriorCompleteness.residualSpace q u e =>
        k.val (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))) hz
      norm_num [coefficient] at he

theorem allowed_qqql (q l : Representation ℂ H ℂ) :
    Allowed (QqqlExchange.residualSpace q l) ↔ Neutral q q q l := by
  constructor
  · rintro ⟨k,hk⟩
    by_contra hn
    apply hk
    apply Subtype.ext
    funext i j
    have hi : ¬ Allowed (Four q q q l) := by rwa [allowed_four]
    exact (forbidden_iff_not_allowed _).mpr hi (k.val i j)
  · intro h
    have hc : ∀ g, (q g 1)^2 * q g 1 * l g 1 = 1 := by
      intro g
      have hg := h g
      linear_combination hg
    let e := QqqlScalarFlavor.residualEquiv q l hc
    refine ⟨e.symm 1, ?_⟩
    intro hz
    have he := congrArg e hz
    simp at he

theorem allowed_total (f : DeltaLOneSignedInput.Species → Representation ℂ H ℂ) :
    Allowed (DeltaLOneSignedFields.Sector f 1) ↔
      Neutral (f 2) (f 1) (f 0) (f 3) ∨
      Neutral (f 0) (f 0) (f 1) (f 4) ∨
      Neutral (f 0) (f 0) (f 0) (f 3) ∨
      Neutral (f 1) (f 1) (f 2) (f 4) := by
  rw [Allowed, DeltaLOneCoefficientCompleteness.nonzero_iff]
  change Allowed (Four (f 2) (f 1) (f 0) (f 3)) ∨
    Allowed (QquePhysicalExteriorCompleteness.residualSpace (f 0) (f 1) (f 4)) ∨
    Allowed (QqqlExchange.residualSpace (f 0) (f 3)) ∨
    Allowed (Four (f 1) (f 1) (f 2) (f 4)) ↔ _
  rw [allowed_four, allowed_qque, allowed_qqql, allowed_four]

end
end GUT.ScalarResidualSelection
