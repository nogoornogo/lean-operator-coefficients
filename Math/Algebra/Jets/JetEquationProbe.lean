import Math.Algebra.Jets.JetEquation

/-! Null-symbol evaluation detects retained higher on-shell jets. -/
namespace Math.JetEquation
set_option autoImplicit false
noncomputable section
open JetDirections MvPolynomial

variable {I : Type*} (q : Symbols I) (x : I → ℂ)

def symbolProbe : JetLinear.Jet Unit I →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun j => eval x (monomial j.2 1))

theorem symbolProbe_ofSymbols (s : Unit) (p : Symbols I) :
    symbolProbe x (ofSymbols s p) = eval x p := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ofSymbols_monomial]
    simp only [symbolProbe, Finsupp.linearCombination_single]
    rw [show monomial α c = c • monomial α (1 : ℂ) by simp [smul_monomial]]
    simp
  | add p r hp hr => simp only [map_add, hp, hr]

theorem symbolProbe_annihilates (hq : eval x q = 0) : relations Unit q ≤ (symbolProbe x).ker := by
  apply Submodule.span_le.mpr
  rintro v ⟨s, p, rfl⟩
  change symbolProbe x (ofSymbols s (p * q)) = 0
  rw [symbolProbe_ofSymbols, map_mul, hq, mul_zero]

def onShellProbe (hq : eval x q = 0) : Generator Unit q →ₗ[ℂ] ℂ :=
  (relations Unit q).liftQ (symbolProbe x) (symbolProbe_annihilates q x hq)

@[simp] theorem onShellProbe_mk (hq : eval x q = 0) (v : JetLinear.Jet Unit I) :
    onShellProbe q x hq ((relations Unit q).mkQ v) = symbolProbe x v := rfl

theorem generator_survives (hq : eval x q = 0) (p : Symbols I) (hp : eval x p ≠ 0) :
    (relations Unit q).mkQ (ofSymbols () p) ≠ 0 := by
  intro h
  have he := congrArg (onShellProbe q x hq) h
  have ha : onShellProbe q x hq ((relations Unit q).mkQ (ofSymbols () p)) = eval x p :=
    symbolProbe_ofSymbols x () p
  rw [ha, map_zero] at he
  exact hp he

end
end Math.JetEquation
