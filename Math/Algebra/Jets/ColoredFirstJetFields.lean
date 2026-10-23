import Math.Algebra.Constructions.ColoredQuarticWords
import Math.Algebra.Jets.JetLinear
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Multilinear field slots for quartic first jets. Derivative directions
are retained separately from the four internal field-vector arguments. -/
namespace Math.ColoredFirstJetFields
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra ColoredQuarticWords
variable {S : Type*}
abbrev Fields (S : Type*) := JetLinear.Field S

def fieldMap : Fields S →ₗ[ℂ] ScalarJetAlgebra.Algebra S (Fin 4) :=
  JetLinear.linearForm.comp (JetLinear.atOrder 0)

@[simp] theorem fieldMap_single (s : S) :
    fieldMap (Finsupp.single s 1) = (MvPolynomial.X (s,0) : ScalarJetAlgebra.Algebra S (Fin 4)) := by
  simp [fieldMap,JetLinear.linearForm]

def base : MultilinearMap ℂ (fun _ : Fin 4 => Fields S) (ScalarJetAlgebra.Algebra S (Fin 4)) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin 4) (ScalarJetAlgebra.Algebra S (Fin 4))).compLinearMap
    (fun _ => fieldMap)

def first (u : Dir) : MultilinearMap ℂ (fun _ : Fin 4 => Fields S)
    (ScalarJetAlgebra.Algebra S (Fin 4)) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin 4) (ScalarJetAlgebra.Algebra S (Fin 4))).compLinearMap
    (fun t => if t = 0 then (dirD u).toLinearMap.comp fieldMap else fieldMap)

theorem base_apply (v : Fin 4 → Fields S) : base v = ∏ t : Fin 4, fieldMap (v t) := rfl

theorem first_apply (v : Fin 4 → Fields S) (u : Dir) :
    first u v = dirD u (fieldMap (v 0))*fieldMap (v 1)*fieldMap (v 2)*fieldMap (v 3) := by
  simp [first,Fin.prod_univ_four]

theorem first_basis (b : Fin 4 → S) (i : Fin 4) :
    first (E i) (fun t => Finsupp.single (b t) 1) =
      ScalarJetAlgebra.totalDerivative i (MvPolynomial.X (b 0,0))*MvPolynomial.X (b 1,0)*
        MvPolynomial.X (b 2,0)*MvPolynomial.X (b 3,0) := by
  rw [first_apply]
  simp only [fieldMap_single,dirD_single,one_smul]

theorem multilinear_ext {f g : MultilinearMap ℂ (fun _ : Fin 4 => Fields S) ℂ}
    (h : ∀ b : Fin 4 → S, f (fun t => Finsupp.single (b t) 1) =
      g (fun t => Finsupp.single (b t) 1)) : f = g := by
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 =>
    (Finsupp.basisSingleOne : Module.Basis S ℂ (Fields S)))
  intro b
  simpa only [Finsupp.coe_basisSingleOne] using h b

end
end Math.ColoredFirstJetFields
