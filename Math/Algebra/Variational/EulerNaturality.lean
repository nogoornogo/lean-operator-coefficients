import Math.Algebra.Jets.LinearJetSubstitution

/-! Euler naturality under compatible constant linear field/direction maps.
Only generator, parity and derivative compatibility are supplied. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
open CoefficientTransport
variable {F B I : Type*}
@[reducible] local instance naturalAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance naturalModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance naturalRing : Ring (A F B I) := inferInstance

/-- Pair a jet vector with a coefficient by formal integration by parts. -/
def adjointPair (v : JetSpace F B I) : A F B I →ₗ[ℂ] (Field F B →₀ A F B I) :=
  eulerMap.comp (spread v)

@[simp] theorem adjointPair_single (j : JetIndex F B I) (c : ℂ) (a : A F B I) :
    adjointPair (Finsupp.single j c) a = Finsupp.single j.1 (c • indexAdjoint j.2 a) := by
  simp [adjointPair]

@[simp] theorem adjointPair_zero (a : A F B I) : adjointPair (0 : JetSpace F B I) a = 0 := by
  simp [adjointPair]

theorem adjointPair_add (v w : JetSpace F B I) (a : A F B I) :
    adjointPair (v+w) a = adjointPair v a+adjointPair w a := by
  simp only [adjointPair,LinearMap.comp_apply,spread_add,map_add]

theorem adjointPair_smul (c : ℂ) (v : JetSpace F B I) (a : A F B I) :
    adjointPair (c • v) a = c • adjointPair v a := by simp [adjointPair]

theorem adjointPair_sum {J : Type*} (s : Finset J) (v : J → JetSpace F B I) (a : A F B I) :
    adjointPair (∑ j ∈ s, v j) a = ∑ j ∈ s, adjointPair (v j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert,hj,adjointPair_add,ih]

theorem adjointPair_shift (i : I) (v : JetSpace F B I) (a : A F B I) :
    adjointPair (JetLinear.shift i v) a = adjointPair v (-D i a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,adjointPair_add,hv,hw]
  | single j c => simp [JetLinear.shift_single,ScalarJetAlgebra.shift,indexAdjoint_shift]

theorem adjointPair_atOrder_zero (v : Field F B →₀ ℂ) (a : A F B I) :
    adjointPair (JetLinear.atOrder 0 v) a = spread v a := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,adjointPair_add,hv,hw,spread_add]
  | single j c => simp

/-- Constant field and direction compatibility for a linear jet substitution.
The field map may be noninvertible for naturality itself. -/
structure Prolongation (F B I : Type*) [Fintype I] extends LinearSubstitution F B I where
  fields : (Field F B →₀ ℂ) →ₗ[ℂ] (Field F B →₀ ℂ)
  directions : I → I → ℂ
  base_map : ∀ v, jets (JetLinear.atOrder 0 v) = JetLinear.atOrder 0 (fields v)
  shift_map : ∀ i v, jets (JetLinear.shift i v) =
    ∑ j, directions i j • JetLinear.shift j (jets v)
  derivative_map : ∀ i a, algebra (D i a) = ∑ j, directions i j • D j (algebra a)

namespace Prolongation
variable [Fintype I] (T : Prolongation F B I)

/-- The formal adjoint cancels the prolonged direction transformation. -/
theorem adjoint_natural (v : JetSpace F B I) (a : A F B I) :
    adjointPair (T.jets v) (T.algebra a) =
      push T.fields T.algebra.toLinearMap (adjointPair v a) := by
  have hw (s : Field F B) (w : List I) (a : A F B I) :
      adjointPair (T.jets (Finsupp.single (s,Expr.wordIndex w) 1)) (T.algebra a) =
        push T.fields T.algebra.toLinearMap
          (Finsupp.single s (VariationalIBP.adjoint D w a)) := by
    induction w generalizing a with
    | nil =>
      have hb := T.base_map (Finsupp.single s 1)
      simp only [JetLinear.atOrder_single] at hb
      rw [show Expr.wordIndex ([] : List I) = 0 from rfl,hb,adjointPair_atOrder_zero]
      simp [VariationalIBP.adjoint]
    | cons i w ih =>
      rw [show Finsupp.single (s,Expr.wordIndex (i::w)) (1:ℂ) =
          JetLinear.shift i (Finsupp.single (s,Expr.wordIndex w) 1) from by
            simp [Expr.wordIndex,ScalarJetAlgebra.shift],
        T.shift_map,adjointPair_sum]
      simp only [adjointPair_smul,adjointPair_shift]
      have hc : T.algebra (-D i a) = ∑ j, T.directions i j • (-D j (T.algebra a)) := by
        rw [map_neg,T.derivative_map]
        simp only [smul_neg,Finset.sum_neg_distrib]
      simp only [VariationalIBP.adjoint]
      rw [← ih (-D i a),hc,map_sum]
      simp only [map_smul]
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,adjointPair_add,hv,hw]
  | single j c =>
    obtain ⟨s,b⟩ := j
    obtain ⟨w,rfl⟩ := Expr.wordIndex_surjective b
    have hs : Finsupp.single (s,Expr.wordIndex w) c =
        c • Finsupp.single (s,Expr.wordIndex w) (1:ℂ) := by simp
    rw [hs,map_smul,adjointPair_smul,adjointPair_smul,map_smul,hw]
    simp [indexAdjoint_word]

/-- Naturality of the computed Euler family, including semantic representatives. -/
theorem euler_natural (p q : Expr F B I) (hq : q.eval = T.algebra p.eval) :
    q.euler = push T.fields T.algebra.toLinearMap p.euler := by
  rw [Expr.euler_eq_eulerMap, T.toLinearSubstitution.gradient_natural p q hq,
    Expr.euler_eq_eulerMap]
  have he : eulerMap.comp T.toLinearSubstitution.gradientMap =
      (push T.fields T.algebra.toLinearMap).comp eulerMap := by
    apply Finsupp.lhom_ext
    intro j a
    simpa [adjointPair,LinearSubstitution.gradientMap] using
      T.adjoint_natural (Finsupp.single j 1) a
  exact LinearMap.congr_fun he p.gradient
end Prolongation

end
end Math.LocalPolynomial
