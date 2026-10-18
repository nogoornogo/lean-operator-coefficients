import Physics.StandardModel.Operators.DipolePolynomialInputs
import Physics.StandardModel.Operators.DipoleMediatorControls

open Math

/-! Polynomial samples with correlated weights. These are not UV models. -/
namespace GUT.DipolePolynomialControls
set_option autoImplicit false
noncomputable section
open MvPolynomial DipoleControls

def polynomials (i : Fin 2) : MvPolynomial Unit ℂ :=
  if i = 0 then X () else (X ())^2

def weights (x : Unit → ℂ) (i : Fin 2) : ℂ := eval x (polynomials i)

def generation (x : Unit → ℂ) : DipoleFlavorSelection.Coefficients flavor flavor :=
  DipolePolynomialInputs.generation flavor flavor flavor
    DipoleMediatorControls.incoming DipoleMediatorControls.outgoing
    DipoleMediatorControls.weakOutgoing polynomials x

theorem selected (x : Unit → ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron (generation x) =
    (x () - (x ())^2, 0) := by
  rw [generation, DipoleMediatorPaths.selected]
  simp [polynomials, DipoleMediatorControls.incoming, DipoleMediatorControls.outgoing,
    DipoleMediatorControls.weakOutgoing, Fin.sum_univ_two, sub_eq_add_neg]

/-- Neither of these two paths can be isolated with a unit weight. -/
theorem not_isolates : ¬ WeightedSelectedPaths.Isolates weights := by
  intro h
  obtain ⟨x, hx, hrest⟩ := h 0
  have hother := hrest 1 (by decide)
  have hz : x () = 1 := by simpa [weights, polynomials] using hx
  have hs : (x ())^2 = 0 := by simpa [weights, polynomials] using hother
  rw [hz] at hs
  norm_num at hs

theorem realized : ∃ x, DipoleFlavorSelection.selector flavor flavor mu electron
    (generation x) ≠ 0 := by
  refine ⟨fun _ => 2, ?_⟩
  rw [selected]
  norm_num

/-- Identical polynomial dependence groups opposing paths into a zero total. -/
theorem same_monomial_cancels (x : Unit → ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (DipolePolynomialInputs.generation flavor flavor flavor
        DipoleMediatorControls.incoming DipoleMediatorControls.outgoing
        DipoleMediatorControls.weakOutgoing (fun _ : Fin 2 => X ()) x) = 0 := by
  rw [DipoleMediatorPaths.selected]
  simp [DipoleMediatorControls.incoming, DipoleMediatorControls.outgoing,
    DipoleMediatorControls.weakOutgoing, Fin.sum_univ_two]

end
end GUT.DipolePolynomialControls
