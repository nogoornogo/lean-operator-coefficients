import Physics.StandardModel.Operators.SixQuarkFlavorCoordinates

open Math

/-! The independently classified 25 local contractions, restricted by the
common generator-statistics theorem. This is the local factor, not a claim that
flavored six-quark coefficients always have two scalar coordinates. -/
namespace GUT.SixQuarkPermutationCompleteness
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient

def invariantSubmodule : Submodule ℂ Coefficient where
  carrier := {f | IsInvariant f}
  zero_mem' := by constructor <;> intro g v <;> rfl
  add_mem' := by
    intro f h hf hh
    constructor
    · intro g v; change f _ + h _ = f v + h v; rw [hf.1, hh.1]
    · intro g v; change f _ + h _ = f v + h v; rw [hf.2, hh.2]
  smul_mem' := by
    intro z f hf
    constructor
    · intro g v; change z • f _ = z • f v; rw [hf.1]
    · intro g v; change z • f _ = z • f v; rw [hf.2]

def coordinatesEquiv : invariantSubmodule ≃ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) where
  toFun f := coordinates f.val
  invFun c := ⟨reconstruct c, reconstruct_invariant c⟩
  left_inv f := by apply Subtype.ext; exact reconstruct_coordinates f.val f.property
  right_inv := coordinates_reconstruct
  map_add' f h := SixQuarkFlavorCoordinates.coordinateLinear.map_add f.val h.val
  map_smul' z f := SixQuarkFlavorCoordinates.coordinateLinear.map_smul z f.val

def targetAction (g : Fin 4) : (Fin 5 → Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) where
  toFun c := transform c g
  map_add' c d := by
    ext p q
    simp [transform, mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    ext p q
    simp [transform, smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- The source really permutes quark slots. Invariance is proved by the
independent reconstruction compatibility, not added as a hypothesis. -/
def sourceAction (g : Fin 4) : invariantSubmodule →ₗ[ℂ] invariantSubmodule where
  toFun f := ⟨f.val.domDomCongr (slotSwap g), by
    rw [← reconstruct_coordinates f.val f.property, ← reconstruct_transform]
    exact reconstruct_invariant _⟩
  map_add' f h := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

theorem compatible (g : Fin 4) (f : invariantSubmodule) :
    coordinatesEquiv (sourceAction g f) = targetAction g (coordinatesEquiv f) := by
  change coordinates (f.val.domDomCongr (slotSwap g)) = transform (coordinates f.val) g
  rw [← reconstruct_coordinates f.val f.property, ← reconstruct_transform,
    coordinates_reconstruct, coordinates_reconstruct]

def equiv : StatisticalCompleteness.sector sourceAction (fun _ => (-1 : ℂ)) ≃ₗ[ℂ]
    StatisticalCompleteness.sector targetAction (fun _ => (-1 : ℂ)) :=
  StatisticalCompleteness.equiv coordinatesEquiv sourceAction targetAction
    (fun _ => -1) compatible

theorem target_iff (c : Fin 5 → Fin 5 → ℂ) :
    c ∈ StatisticalCompleteness.sector targetAction (fun _ => (-1 : ℂ)) ↔
      SatisfiesStatistics c := by
  change (∀ g, transform c g = (-1 : ℂ) • c) ↔ ∀ g p q, residual c g p q = 0
  simp only [neg_one_smul]
  constructor
  · intro h g p q
    change c p q + transform c g p q = 0
    rw [h g]; simp
  · intro h g
    ext p q
    exact eq_neg_of_add_eq_zero_right (h g p q)

theorem source_iff (f : invariantSubmodule) :
    f ∈ StatisticalCompleteness.sector sourceAction (fun _ => (-1 : ℂ)) ↔
      IsSpeciesAlternating f.val := by
  constructor
  · intro h p hp v
    apply generators_species_sign f.val _ p hp v
    intro g w
    have he := congrArg (fun z : invariantSubmodule => z.val w) (h g)
    simpa [sourceAction, MultilinearMap.domDomCongr_apply, Function.comp_def] using he
  · intro h g
    apply Subtype.ext
    ext v
    have hp : SixSlotAlternation.PreservesPattern (slotSwap g) := by
      fin_cases g <;> decide
    have he := h (slotSwap g) hp v
    fin_cases g <;> simpa [sourceAction, slotSwap, Function.comp_def] using he

@[simp] theorem extraction (f : StatisticalCompleteness.sector sourceAction
    (fun _ => (-1 : ℂ))) :
    (equiv f).val = coordinates f.val.val := rfl

@[simp] theorem reconstruction (c : StatisticalCompleteness.sector targetAction
    (fun _ => (-1 : ℂ))) :
    (equiv.symm c).val.val = reconstruct c.val := rfl

def sourceEquiv : admissible ≃ₗ[ℂ]
    StatisticalCompleteness.sector sourceAction (fun _ => (-1 : ℂ)) where
  toFun f := ⟨⟨f.val, f.property.1⟩, (source_iff _).mpr f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, (source_iff _).mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def targetEquiv : StatisticalCompleteness.sector targetAction (fun _ => (-1 : ℂ))
    ≃ₗ[ℂ] statisticsKernel where
  toFun c := ⟨c.val, (target_iff _).mp c.property⟩
  invFun c := ⟨c.val, (target_iff _).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reuse the independent two-probe normalization only after transporting
the full species sign rule through the common theorem. -/
def twoProbeEquiv : admissible ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  sourceEquiv.trans (equiv.trans (targetEquiv.trans probeEquiv))

theorem twoProbeEquiv_agrees : twoProbeEquiv = coefficientProbeEquiv := by
  apply LinearEquiv.ext
  intro f
  change probeEquiv ⟨coordinates f.val, _⟩ = twoProbes f.val
  rw [probeEquiv_apply, reconstruct_coordinates f.val f.property.1]

theorem inverse_agrees : twoProbeEquiv.symm = coefficientProbeEquiv.symm := by
  rw [twoProbeEquiv_agrees]

end
end GUT.SixQuarkPermutationCompleteness
