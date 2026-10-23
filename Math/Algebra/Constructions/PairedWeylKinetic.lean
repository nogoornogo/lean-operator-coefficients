import Math.RepresentationTheory.Lagrangian.LagrangianInput

/-! Ordered odd kinetic syntax and its complete Euler family, with four
commuting component spectators. Equations are specified independently. -/
namespace Math.PairedWeylKinetic
set_option autoImplicit false
noncomputable section
open LocalPolynomial LocalPolynomial.Expr MixedJetAlgebra
abbrev Label := Bool × Fin 2
abbrev E := Expr Label Label (Fin 4)
abbrev A := LocalPolynomial.A Label Label (Fin 4)
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance
def psi (c : Bool) (a : Fin 2) : A := odd ((c,a),0)
abbrev D := LocalPolynomial.D (F := Label) (B := Label) (I := Fin 4)
def term (a b : Fin 2) (i : Fin 4) : E :=
  fermion (true,a) * jet (.inl (false,b)) [i]
def density : E :=
  term 0 0 0 + term 0 0 3 + term 0 1 1 + Complex.I • term 0 1 2 +
  term 1 0 1 - Complex.I • term 1 0 2 + term 1 1 0 - term 1 1 3

def left (a : Fin 2) : A := if a = 0 then
  D 0 (psi false 0)+D 3 (psi false 0)+D 1 (psi false 1)+Complex.I • D 2 (psi false 1)
  else D 1 (psi false 0)-Complex.I • D 2 (psi false 0)+D 0 (psi false 1)-D 3 (psi false 1)
def right (a : Fin 2) : A := if a = 0 then
  D 0 (psi true 0)+D 3 (psi true 0)+D 1 (psi true 1)-Complex.I • D 2 (psi true 1)
  else D 1 (psi true 0)+Complex.I • D 2 (psi true 0)+D 0 (psi true 1)-D 3 (psi true 1)
def seed (j : Label) : A := if j.1 then right j.2 else left j.2
def seeds : Set A := Set.range seed

theorem seed_false (a : Fin 2) : seed (false,a) = left a := by simp [seed]
theorem seed_true (a : Fin 2) : seed (true,a) = right a := by simp [seed]

theorem term_odd (a b : Fin 2) (i : Fin 4) (j : Label) :
    (term a b i).euler (.inl j) =
      (if j = (true,a) then D i (psi false b) else 0) +
      (if j = (false,b) then D i (psi true a) else 0) := by
  classical
  simp [term,Expr.fermion,Expr.euler,linearize,eulerTerms,twist,
    Expr.eval,VariationalIBP.adjoint,wordIndex,psi,
    MixedJetAlgebra.totalDerivative_odd,ScalarJetAlgebra.shift,
    Finsupp.single_apply,eq_comm]

theorem term_even (a b : Fin 2) (i : Fin 4) (j : Label) :
    (term a b i).euler (.inr j) = 0 := by
  classical
  simp [term,Expr.fermion,Expr.euler,linearize,eulerTerms,twist,
    Expr.eval,VariationalIBP.adjoint]

theorem generated_odd (j : Label) : density.euler (.inl j) = seed (!j.1,j.2) := by
  obtain ⟨c,a⟩ := j
  cases c <;> fin_cases a <;>
    simp [density,euler_add,euler_sub,euler_smul,term_odd,seed,left,right]

theorem generated_even (j : Label) : density.euler (.inr j) = 0 := by
  simp [density,euler_add,euler_sub,euler_smul,term_even]

theorem equations_equal : density.equations = TwoSidedDifferential.relations D seeds := by
  apply le_antisymm
  · apply TwoSidedDifferential.minimal
    · rintro _ ⟨s,rfl⟩
      cases s with
      | inl j => rw [generated_odd]; exact TwoSidedDifferential.seed_mem _ _ ⟨_,rfl⟩
      | inr j => rw [generated_even]; exact Submodule.zero_mem _
    · exact fun a p hp => TwoSidedDifferential.left_mem _ _ a hp
    · exact fun a p hp => TwoSidedDifferential.right_mem _ _ a hp
    · exact fun i p hp => TwoSidedDifferential.derivative_mem _ _ i hp
  · apply TwoSidedDifferential.minimal
    · rintro _ ⟨⟨c,a⟩,rfl⟩
      have h := density.euler_mem (.inl (!c,a))
      rw [generated_odd] at h
      cases c <;> exact h
    · exact fun a p hp => TwoSidedDifferential.left_mem _ _ a hp
    · exact fun a p hp => TwoSidedDifferential.right_mem _ _ a hp
    · exact fun i p hp => TwoSidedDifferential.derivative_mem _ _ i hp

theorem relations_equal : density.relations = TwoSidedDifferential.combined D seeds := by
  change density.equations ⊔ _ = _
  rw [equations_equal]
  rfl
end
end Math.PairedWeylKinetic
