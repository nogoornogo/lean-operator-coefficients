import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Physics.StandardModel.Operators.ResidualSelectionCriteria
import Physics.StandardModel.Operators.CyclicResidualSelection

open Math

/-! Scalar characters retain the full typed six-quark statistics constraints. -/
namespace GUT.DeltaBTwoScalarSelection
set_option autoImplicit false
noncomputable section
open SixQuarkTypedFlavor SixQuarkFlavorCoordinates DeltaBTwoFlavorOneGeneration
open SelectionCriteria
open scoped TensorProduct
variable {H : Type*} [Group H]

def total (up down : Representation ℂ H ℂ) (g : H) : ℂ :=
  (up g 1)^2 * (down g 1)^4

def Neutral (up down : Representation ℂ H ℂ) : Prop := ∀ g, total up down g = 1

theorem scalar_map (r : Representation ℂ H ℂ) (g : H) :
    r g = (r g 1) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  calc
    r g x = r g (x • (1 : ℂ)) := by simp
    _ = _ := by rw [map_smul]; simp [mul_comm]

theorem slot_action (up down : Representation ℂ H ℂ) (g : H) (i : Fin 6)
    (v : SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor ℂ ℂ i) :
    TensorProduct.map LinearMap.id (slotRepresentation ℂ ℂ up down i g) v =
      (if i = 0 ∨ i = 2 then up g 1 else down g 1) • v := by
  fin_cases i
  all_goals first
    | change TensorProduct.map LinearMap.id (up g) v = (up g 1) • v
    | change TensorProduct.map LinearMap.id (down g) v = (down g 1) • v
  all_goals rw [scalar_map]
  all_goals simp only [TensorProduct.map_smul_right, TensorProduct.map_id,
    LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]

theorem residual_action (up down : Representation ℂ H ℂ)
    (f : FlavorCoefficient (V := SlotFlavor ℂ ℂ)) (g : H) (v) :
    f (fun i => TensorProduct.map LinearMap.id
      (slotRepresentation ℂ ℂ up down i g) (v i)) = total up down g * f v := by
  simp_rw [slot_action]
  rw [MultilinearMap.map_smul_univ]
  simp only [Fin.prod_univ_succ, total, smul_eq_mul]
  change (up g 1 * (down g 1 * (up g 1 * (down g 1 * (down g 1 * (down g 1 * 1)))))) * f v = _
  ring

theorem neutral_invariant (up down : Representation ℂ H ℂ) (h : Neutral up down)
    (f : FlavorCoefficient (V := SlotFlavor ℂ ℂ)) :
    IsResidualInvariant (slotRepresentation ℂ ℂ up down) f := by
  intro g v
  rw [residual_action, h g, one_mul]

def coefficientEquiv (up down : Representation ℂ H ℂ) (h : Neutral up down) :
    Coefficients ℂ ℂ up down ≃ₗ[ℂ] Coefficients ℂ ℂ scalar scalar where
  toFun f := ⟨f.val, f.property.1, neutral_invariant scalar scalar (by intro g; simp [total, scalar]) f.val,
    f.property.2.2⟩
  invFun f := ⟨f.val, f.property.1, neutral_invariant up down h f.val, f.property.2.2⟩
  left_inv f := by rfl
  right_inv f := by rfl
  map_add' f k := by rfl
  map_smul' z f := by rfl

def twoProbeEquiv (up down : Representation ℂ H ℂ) (h : Neutral up down) :
    DeltaBTwoModelInterface.ModelSector up down ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (DeltaBTwoFlavorBridge.sectorCoefficientEquiv up down).trans
    ((coefficientEquiv up down h).trans (typedScalarEquiv.trans
      SixQuarkSpeciesQuotient.coefficientProbeEquiv))

def pairEquiv (up down : Representation ℂ H ℂ) (h : Neutral up down) :
    DeltaBTwoModelInterface.ModelSector up down ≃ₗ[ℂ] ℂ × ℂ :=
  (twoProbeEquiv up down h).trans (LinearEquiv.finTwoArrow ℂ ℂ)

theorem reconstruct_twoProbes (up down : Representation ℂ H ℂ) (h : Neutral up down)
    (t : Fin 2 → ℂ) :
    twoProbeEquiv up down h ((twoProbeEquiv up down h).symm t) = t :=
  (twoProbeEquiv up down h).apply_symm_apply t

theorem allowed_iff (up down : Representation ℂ H ℂ) :
    Allowed (DeltaBTwoModelInterface.ModelSector up down) ↔ Neutral up down := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (allowed_equiv
      (DeltaBTwoFlavorBridge.sectorCoefficientEquiv up down)).mp h
    have hv : ∃ v, f.val v ≠ 0 := by
      by_contra hn
      apply hf
      apply Subtype.ext
      ext v
      simpa using (not_exists.mp hn v)
    obtain ⟨v, hv⟩ := hv
    intro g
    have hi := f.property.2.1 g v
    rw [residual_action] at hi
    exact mul_right_cancel₀ hv (hi.trans (one_mul _).symm)
  · intro h
    apply (allowed_equiv (twoProbeEquiv up down h)).mpr
    exact ⟨fun _ => 1, by intro hz; have := congrFun hz 0; simp at this⟩

theorem forbidden_iff (up down : Representation ℂ H ℂ) :
    Forbidden (DeltaBTwoModelInterface.ModelSector up down) ↔ ¬ Neutral up down := by
  rw [forbidden_iff_not_allowed, allowed_iff]

theorem finrank_neutral (up down : Representation ℂ H ℂ) (h : Neutral up down) :
    Module.finrank ℂ (DeltaBTwoModelInterface.ModelSector up down) = 2 := by
  rw [(twoProbeEquiv up down h).finrank_eq]
  simp

theorem inverse_twoProbes (up down : Representation ℂ H ℂ) (h : Neutral up down)
    (f : DeltaBTwoModelInterface.ModelSector up down) :
    (twoProbeEquiv up down h).symm (twoProbeEquiv up down h f) = f :=
  (twoProbeEquiv up down h).symm_apply_apply f

section ActualFields
variable (up down : Representation ℂ H ℂ)
  {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup H) A)
  (b : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup H) B)
  (input : DeltaBTwoModelInterface.Inputs up down a b)

def onFieldsTwoProbeEquiv (h : Neutral up down) :
    SixSlotSpeciesDegree.sector a b ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (DeltaBTwoModelInterface.onFieldsEquiv up down a b input).symm.trans
    (twoProbeEquiv up down h)

include input in
theorem allowed_onFields_iff :
    Allowed (SixSlotSpeciesDegree.sector a b) ↔ Neutral up down := by
  rw [← allowed_equiv (DeltaBTwoModelInterface.onFieldsEquiv up down a b input)]
  exact allowed_iff up down

include input in
theorem forbidden_onFields_iff :
    Forbidden (SixSlotSpeciesDegree.sector a b) ↔ ¬ Neutral up down := by
  rw [forbidden_iff_not_allowed, allowed_onFields_iff up down a b input]
end ActualFields

end
end GUT.DeltaBTwoScalarSelection
