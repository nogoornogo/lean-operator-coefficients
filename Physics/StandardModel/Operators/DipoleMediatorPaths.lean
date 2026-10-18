import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.LinearAlgebra.WeightedSelectedPaths

open Math

/-! Algebraic mediator factorization of generated dipoles. No UV matching
calculation is asserted: actual models must supply the factorization equality. -/
namespace GUT.DipoleMediatorPaths
set_option autoImplicit false
noncomputable section
open Representation

variable {H A B M I X : Type*} [Group H] [Fintype I]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup M] [Module ℂ M]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (m : Representation ℂ H M)
  (incoming : I → IntertwiningMap a m)
  (outB outW : I → IntertwiningMap m b)

def paths (i : I) : IntertwiningMap a b × IntertwiningMap a b :=
  ((outB i).comp (incoming i), (outW i).comp (incoming i))

variable [FiniteDimensional ℂ B] (w : X → I → ℂ)

def generation (x : X) : DipoleFlavorSelection.Coefficients a b :=
  (DipoleSMCoefficient.equiv a b).symm
    (WeightedSelectedPaths.synthesis (paths a b m incoming outB outW) w x)

variable (mu : A) (electron : Module.Dual ℂ B)

omit [Fintype I] [FiniteDimensional ℂ B] in
theorem path_selected (i : I) :
    DipoleFlavorSelection.residualSelector a b mu electron
      (paths a b m incoming outB outW i) =
    (electron (outB i (incoming i mu)), electron (outW i (incoming i mu))) := rfl

theorem selected (x : X) :
    DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) =
    ∑ i, w x i •
      (electron (outB i (incoming i mu)), electron (outW i (incoming i mu))) := by
  change DipoleFlavorSelection.residualSelector a b mu electron
    ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
  rw [LinearEquiv.apply_symm_apply, WeightedSelectedPaths.selected]
  rfl

theorem nonzero_iff (x : X) :
    DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) ≠ 0 ↔
    (∑ i, w x i •
      (electron (outB i (incoming i mu)), electron (outW i (incoming i mu)))) ≠ 0 := by
  rw [selected]

/-- Existence becomes a pathwise structural criterion when actual inputs can
isolate each path. Nonzero paths may still cancel at other inputs. -/
theorem exists_nonzero_iff_path (hw : WeightedSelectedPaths.Isolates w) :
    (∃ x, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) ≠ 0) ↔
    ∃ i, electron (outB i (incoming i mu)) ≠ 0 ∨
      electron (outW i (incoming i mu)) ≠ 0 := by
  have h := WeightedSelectedPaths.exists_nonzero_iff_path
    (DipoleFlavorSelection.residualSelector a b mu electron)
    (paths a b m incoming outB outW) w hw
  have he : ∀ x, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) =
      DipoleFlavorSelection.residualSelector a b mu electron
        (WeightedSelectedPaths.synthesis (paths a b m incoming outB outW) w x) := by
    intro x
    change DipoleFlavorSelection.residualSelector a b mu electron
      ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  simp only [he, path_selected] at *
  simpa only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or] using h

theorem nonzero_of_single_selected_path (i : I) (x : X)
    (hi : w x i ≠ 0)
    (hp : electron (outB i (incoming i mu)) ≠ 0 ∨
      electron (outW i (incoming i mu)) ≠ 0)
    (hrest : ∀ j, j ≠ i → w x j •
      (electron (outB j (incoming j mu)), electron (outW j (incoming j mu))) = 0) :
    DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) ≠ 0 := by
  rw [selected, Finset.sum_eq_single i]
  · apply smul_ne_zero hi
    simpa only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or] using hp
  · intro j _ hji
    exact hrest j hji
  · simp

/-- A concrete mediator vector reached with nonzero amplitude and detected by
the outgoing B map is sufficient, provided other selected paths vanish. -/
theorem nonzero_of_mediator_witness (i : I) (x : X) (v : M) (t : ℂ)
    (hin : incoming i mu = t • v) (ht : t ≠ 0)
    (hout : electron (outB i v) ≠ 0) (hi : w x i ≠ 0)
    (hrest : ∀ j, j ≠ i → w x j •
      (electron (outB j (incoming j mu)), electron (outW j (incoming j mu))) = 0) :
    DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW w x) ≠ 0 := by
  apply nonzero_of_single_selected_path a b m incoming outB outW w mu electron i x hi
    (Or.inl ?_) hrest
  rw [hin, map_smul, map_smul, smul_eq_mul]
  exact mul_ne_zero ht hout

/-- Apply the structural calculation to an externally supplied, possibly
nonlinear generation map, keeping its model factorization obligation explicit. -/
theorem selected_of_factorization (F : X → DipoleFlavorSelection.Coefficients a b)
    (x : X) (hF : (DipoleSMCoefficient.equiv a b) (F x) =
      WeightedSelectedPaths.synthesis (paths a b m incoming outB outW) w x) :
    DipoleFlavorSelection.selector a b mu electron (F x) =
    ∑ i, w x i •
      (electron (outB i (incoming i mu)), electron (outW i (incoming i mu))) := by
  change DipoleFlavorSelection.residualSelector a b mu electron
    ((DipoleSMCoefficient.equiv a b) (F x)) = _
  rw [hF, WeightedSelectedPaths.selected]
  rfl

theorem realized_iff_path_of_factorization
    (F : X → DipoleFlavorSelection.Coefficients a b)
    (hF : ∀ x, (DipoleSMCoefficient.equiv a b) (F x) =
      WeightedSelectedPaths.synthesis (paths a b m incoming outB outW) w x)
    (hw : WeightedSelectedPaths.Isolates w) :
    (∃ x, DipoleFlavorSelection.selector a b mu electron (F x) ≠ 0) ↔
    ∃ i, electron (outB i (incoming i mu)) ≠ 0 ∨
      electron (outW i (incoming i mu)) ≠ 0 := by
  have he : F = generation a b m incoming outB outW w := by
    funext x
    apply (DipoleSMCoefficient.equiv a b).injective
    simpa only [generation, LinearEquiv.apply_symm_apply] using hF x
  rw [he]
  exact exists_nonzero_iff_path a b m incoming outB outW w mu electron hw

end
end GUT.DipoleMediatorPaths
