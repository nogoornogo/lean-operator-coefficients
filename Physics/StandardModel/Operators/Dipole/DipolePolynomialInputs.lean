import Physics.StandardModel.Operators.Dipole.DipoleMediatorPaths
import Math.LinearAlgebra.Selection.PolynomialSelectedPaths

open Math

/-! Structural nonvanishing criteria for polynomially weighted residual paths.
Free coordinates and polynomial factorization are explicit model obligations. -/
namespace Physics.DipolePolynomialInputs
set_option autoImplicit false
noncomputable section
open Representation MvPolynomial

variable {H A B M I S : Type*} [Group H] [Fintype I]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (m : Representation ℂ H M)
  (incoming : I → IntertwiningMap a m)
  (outB outW : I → IntertwiningMap m b)
  (p : I → MvPolynomial S ℂ) (mu : A) (electron : Module.Dual ℂ B)

abbrev generation (x : S → ℂ) : DipoleFlavorSelection.Coefficients a b :=
  DipoleMediatorPaths.generation a b m incoming outB outW (fun y i => eval y (p i)) x

theorem exists_nonzero_on_box_iff_coefficient
    (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW p x) ≠ 0) ↔
    ∃ d : S →₀ ℕ,
      (∑ i, electron (outB i (incoming i mu)) * (p i).coeff d) ≠ 0 ∨
      (∑ i, electron (outW i (incoming i mu)) * (p i).coeff d) ≠ 0 := by
  have h := PolynomialSelectedPaths.pair_exists_nonzero_on_box_iff_coefficient
    (DipoleMediatorPaths.paths a b m incoming outB outW) p
    (DipoleFlavorSelection.residualSelector a b mu electron) s hs
  have he : ∀ x, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW p x) =
      DipoleFlavorSelection.residualSelector a b mu electron
        (WeightedSelectedPaths.synthesis (DipoleMediatorPaths.paths a b m incoming outB outW)
          (fun y i => eval y (p i)) x) := by
    intro x
    change DipoleFlavorSelection.residualSelector a b mu electron
      ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  simpa only [he, DipoleMediatorPaths.path_selected] using h

theorem exists_nonzero_monomials_iff_path (degrees : I → S →₀ ℕ)
    (hd : Function.Injective degrees) (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW (fun i => monomial (degrees i) 1) x) ≠ 0) ↔
    ∃ i, electron (outB i (incoming i mu)) ≠ 0 ∨
      electron (outW i (incoming i mu)) ≠ 0 := by
  have h := PolynomialSelectedPaths.pair_exists_nonzero_monomials_iff_path
    (DipoleMediatorPaths.paths a b m incoming outB outW)
    (DipoleFlavorSelection.residualSelector a b mu electron) degrees hd s hs
  have he : ∀ x, DipoleFlavorSelection.selector a b mu electron
      (generation a b m incoming outB outW (fun i => monomial (degrees i) 1) x) =
      DipoleFlavorSelection.residualSelector a b mu electron
        (WeightedSelectedPaths.synthesis (DipoleMediatorPaths.paths a b m incoming outB outW)
          (fun y i => eval y (monomial (degrees i) 1)) x) := by
    intro x
    change DipoleFlavorSelection.residualSelector a b mu electron
      ((DipoleSMCoefficient.equiv a b) ((DipoleSMCoefficient.equiv a b).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  simpa only [he, DipoleMediatorPaths.path_selected, ne_eq, Prod.ext_iff,
    Prod.fst_zero, Prod.snd_zero, not_and_or] using h

theorem realized_iff_coefficient_of_factorization
    (F : (S → ℂ) → DipoleFlavorSelection.Coefficients a b)
    (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite)
    (hF : ∀ x ∈ Set.pi Set.univ s, (DipoleSMCoefficient.equiv a b) (F x) =
      WeightedSelectedPaths.synthesis (DipoleMediatorPaths.paths a b m incoming outB outW)
        (fun y i => eval y (p i)) x) :
    (∃ x ∈ Set.pi Set.univ s, DipoleFlavorSelection.selector a b mu electron (F x) ≠ 0) ↔
    ∃ d : S →₀ ℕ,
      (∑ i, electron (outB i (incoming i mu)) * (p i).coeff d) ≠ 0 ∨
      (∑ i, electron (outW i (incoming i mu)) * (p i).coeff d) ≠ 0 := by
  have he : ∀ x ∈ Set.pi Set.univ s, F x = generation a b m incoming outB outW p x := by
    intro x hx
    apply (DipoleSMCoefficient.equiv a b).injective
    simpa only [generation, DipoleMediatorPaths.generation, LinearEquiv.apply_symm_apply]
      using hF x hx
  have hx : (∃ x ∈ Set.pi Set.univ s, DipoleFlavorSelection.selector a b mu electron (F x) ≠ 0) ↔
      ∃ x ∈ Set.pi Set.univ s, DipoleFlavorSelection.selector a b mu electron
        (generation a b m incoming outB outW p x) ≠ 0 := by
    constructor <;> rintro ⟨x, hx, hn⟩
    · exact ⟨x, hx, by simpa only [he x hx] using hn⟩
    · exact ⟨x, hx, by simpa only [he x hx] using hn⟩
  exact hx.trans (exists_nonzero_on_box_iff_coefficient a b m incoming outB outW p mu electron s hs)

end
end Physics.DipolePolynomialInputs
