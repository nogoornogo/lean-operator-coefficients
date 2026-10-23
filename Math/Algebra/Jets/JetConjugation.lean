import Math.Algebra.Jets.LinearJetEquation
import Mathlib.Algebra.Star.Module

/-! Coefficient conjugation on ordinary jets fixes every derivative label. -/
namespace Math.JetConjugation
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections
variable {K S I : Type*}

def coefficients : (K →₀ ℂ) →ₛₗ[starRingEnd ℂ] (K →₀ ℂ) :=
  Finsupp.mapRange.linearMap (starLinearEquiv ℂ).toLinearMap

@[simp] theorem coefficients_apply (v : K →₀ ℂ) (k : K) : coefficients v k = star (v k) := rfl

@[simp] theorem coefficients_single (k : K) (c : ℂ) :
    coefficients (Finsupp.single k c) = Finsupp.single k (star c) := by
  classical
  simp [coefficients, Finsupp.mapRange.linearMap_apply]

@[simp] theorem coefficients_involutive (v : K →₀ ℂ) : coefficients (coefficients v) = v := by
  ext k
  simp

def symbols : Symbols I →+* Symbols I := MvPolynomial.map (starRingEnd ℂ)

theorem coefficients_ofSymbols (s : S) (p : Symbols I) :
    coefficients (ofSymbols s p) = ofSymbols s (symbols p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c => simp [ofSymbols_monomial, symbols, MvPolynomial.map_monomial]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coefficients_multiple (p : Symbols I) (v : Jet S I) :
    coefficients (LinearJetEquation.multiple p v) =
      LinearJetEquation.multiple (symbols p) (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, a⟩ := j
    rw [← ofSymbols_monomial, LinearJetEquation.multiple_ofSymbols,
      coefficients_ofSymbols, coefficients_ofSymbols, LinearJetEquation.multiple_ofSymbols, map_mul]

theorem coefficients_shift (i : I) (v : Jet S I) :
    coefficients (JetLinear.shift i v) = JetLinear.shift i (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c => simp

theorem coefficients_atOrder (a : I →₀ ℕ) (v : JetLinear.Field S) :
    coefficients (atOrder a v) = atOrder a (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single s c => simp

theorem coefficients_internal (f g : JetLinear.Field S →ₗ[ℂ] JetLinear.Field S)
    (h : ∀ v, coefficients (f v) = g (coefficients v)) (v : Jet S I) :
    coefficients (JetLinear.map f v) = JetLinear.map g (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, a⟩ := j
    simp [map_smulₛₗ, coefficients_atOrder, h]

theorem symbols_linearForm (v : Direction I) :
    symbols (linearForm v) = linearForm (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i c => simp [linearForm_single, symbols, MvPolynomial.smul_eq_C_mul]

theorem symbols_symbolMap (f : Direction I →ₗ[ℂ] Direction I)
    (h : ∀ i, coefficients (f (Finsupp.single i 1)) = f (Finsupp.single i 1)) (p : Symbols I) :
    symbols (symbolMap f p) = symbolMap f (symbols p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [symbols, symbolMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, symbolMap_X, symbols_linearForm, h]
    simp [symbols, symbolMap_X]

theorem coefficients_direction (f : Direction I →ₗ[ℂ] Direction I)
    (h : ∀ i, coefficients (f (Finsupp.single i 1)) = f (Finsupp.single i 1)) (v : Jet S I) :
    coefficients (jetMap f v) = jetMap f (coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, a⟩ := j
    rw [← ofSymbols_monomial]
    simp only [jetMap, lift_ofSymbols, AlgHom.toLinearMap_apply, coefficients_ofSymbols,
      symbols_symbolMap f h]

end
end Math.JetConjugation
