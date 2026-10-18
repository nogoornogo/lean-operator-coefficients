import Math.RepresentationTheory.AutomorphismCovariantHom

/-! Strict transitive audit of covariant descent and its control interfaces. -/
open Representation
namespace Math.AutomorphismCovariantHom.FiniteControl
abbrev P := Equiv.Perm (Fin 3)
def g : P := Equiv.swap 0 1
def h : P := Equiv.swap 1 2
noncomputable def rho := leftRegular ℚ P
theorem noncommutes : ¬ ∀ v, rho g (rho h v) = rho h (rho g v) := by
  intro hc
  have he := hc (MonoidAlgebra.single (1 : P) (1 : ℚ))
  simp only [rho, leftRegular, ofMulAction_single, smul_eq_mul, mul_one] at he
  have hn : g * h ≠ h * g := by decide
  have ht := congrArg (fun f : MonoidAlgebra ℚ P => f.coeff (g * h)) he
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply] at ht
  simp [Ne.symm hn] at ht
end Math.AutomorphismCovariantHom.FiniteControl

open Lean in
run_cmd do
  let ds := [
    ``Math.AutomorphismCovariantHom.FiniteControl.noncommutes,
    ``Math.AutomorphismCovariantHom.stable,
    ``Math.AutomorphismCovariantHom.equiv,
    ``Math.AutomorphismCovariantHom.equiv_mk,
    ``Math.AutomorphismCovariantHom.forbidden_iff,
    ``Math.AutomorphismCovariantHom.commutes_of_identity,
    ``Math.AutomorphismCovariantHom.conjugationControl,
    ``Math.AutomorphismCovariantHom.conjugationControl_commutes_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Covariant Hom {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Covariant Hom: {ds.length} strict transitive checks passed"
