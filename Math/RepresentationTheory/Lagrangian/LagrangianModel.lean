import Math.RepresentationTheory.Lagrangian.BosonicAllOrderCoordinates
import Math.RepresentationTheory.Lagrangian.LagrangianSymmetry

/-! Additive model packages. Existing generated inputs and their coefficients
are reused definitionally; no new field or equation input format is imposed. -/
namespace Math.AllOrderDerivativeCoordinates.Presentation
set_option autoImplicit false
noncomputable section
variable {H U ι κ T : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  {P : DerivativeInterface.Input H U} (C : Presentation (ι := ι) (κ := κ) P)

theorem target_values_iff (v : T → U) (a : T → ℂ) :
    (∃ f : P.Coefficient, ∀ t, f.val (v t) = a t) ↔
    ∃ q : C.rows, ∀ t, C.assemble q.val (v t) = a t := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨C.equivalence f,?_⟩
    intro t
    have he := congrArg (fun f : P.Coefficient => f.val (v t))
      (C.equivalence.symm_apply_apply f)
    exact he.trans (hf t)
  · rintro ⟨q,hq⟩
    exact ⟨C.equivalence.symm q,hq⟩
end
end Math.AllOrderDerivativeCoordinates.Presentation

namespace Math.LocalPolynomial.Expr
@[simp] theorem eval_sub {F B I : Type*} (p q : Expr F B I) :
    (p-q).eval = p.eval-q.eval := by
  change (p + -q).eval = _
  rw [eval_add,eval_neg,sub_eq_add_neg]
end Math.LocalPolynomial.Expr

namespace Math.LagrangianModel
set_option autoImplicit false
noncomputable section
open LocalPolynomial
variable {F B I H : Type*} [Group H]

structure Mixed (F B I H : Type*) [Group H] where
  density : Expr F B I
  action : Representation ℂ H (A F B I)
  stable : ∀ g, density.relations ≤ density.relations.comap (action g)

structure Bosonic (B I H : Type*) [Group H] where
  density : Expr Empty B I
  action : Representation ℂ H (Scalar B I)
  stable : ∀ g, DifferentialEquation.combined ScalarJetAlgebra.totalDerivative density.scalarSeeds ≤
    (DifferentialEquation.combined ScalarJetAlgebra.totalDerivative density.scalarSeeds).comap (action g)

namespace Mixed
def trivial (p : Expr F B I) : Mixed F B I Unit :=
  ⟨p,Representation.trivial ℂ Unit _,fun _ => le_refl _⟩

def ofEulerSpan [Fintype I] (p : Expr F B I)
    (rho : Representation ℂ H (A F B I))
    (hM : ∀ g u v, rho g (u*v) = rho g u*rho g v)
    (c : H → I → I → ℂ)
    (hD : ∀ g i u, rho g (LocalPolynomial.D i u) =
      ∑ j, c g i j • LocalPolynomial.D j (rho g u))
    (hE : ∀ g s, rho g (p.euler s) ∈ Submodule.span ℂ (Set.range p.euler)) : Mixed F B I H :=
  ⟨p,rho,p.stable_of_euler_span rho hM c hD hE⟩

variable (M : Mixed F B I H)
def input := M.density.input M.action M.stable
def presentation := M.density.allOrderPresentation M.action M.stable
abbrev Coordinates := M.presentation.rows
def equivalence : M.input.Coefficient ≃ₗ[ℂ] M.Coordinates := M.presentation.equivalence
def evaluate (q : M.Coordinates) : A F B I →ₗ[ℂ] ℂ := M.presentation.assemble q.val
theorem evaluate_encode (f : M.input.Coefficient) (u : A F B I) :
    M.evaluate (M.equivalence f) u = f.val u :=
  congrArg (fun f : M.input.Coefficient => f.val u) (M.equivalence.symm_apply_apply f)
theorem target_values_iff {T : Type*} (v : T → A F B I) (a : T → ℂ) :
    (∃ f : M.input.Coefficient, ∀ t, f.val (v t) = a t) ↔
    ∃ q : M.Coordinates, ∀ t, M.evaluate q (v t) = a t := M.presentation.target_values_iff v a
theorem reconstruction (f : M.input.Coefficient) (u : A F B I) :
    f.val u = (M.presentation.basis.repr u).sum (fun i a => a*(M.equivalence f).val i) :=
  M.presentation.reconstruction f u
theorem prescribed_iff (c : LocalPolynomial.Expr.Monomial F B I → ℂ) :
    (∃ f : M.input.Coefficient, ∀ i, f.val (M.presentation.basis i) = c i) ↔
      c ∈ M.Coordinates := M.presentation.prescribed_iff c
theorem forbidden_iff : DerivativeProhibition.Forbids M.input ↔
    SelectionCriteria.Forbidden M.Coordinates := M.presentation.forbidden_iff
theorem allowed_iff : DerivativeProhibition.Allows M.input ↔
    SelectionCriteria.Allowed M.Coordinates := M.presentation.allowed_iff
def selected (V : Submodule ℂ (A F B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.input.select V hV
def selectedPresentation (V : Submodule ℂ (A F B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.presentation.canonicalSelectedPresentation V hV
def selectedEquivalence (V : Submodule ℂ (A F B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.presentation.canonicalSelectedEquivalence V hV
end Mixed

namespace Bosonic
def trivial (p : Expr Empty B I) : Bosonic B I Unit :=
  ⟨p,Representation.trivial ℂ Unit _,fun _ => le_refl _⟩

def ofEulerSpan [Fintype I] (p : Expr Empty B I)
    (rho : Representation ℂ H (Scalar B I))
    (hM : ∀ g u v, rho g (u*v) = rho g u*rho g v)
    (c : H → I → I → ℂ)
    (hD : ∀ g i u, rho g (ScalarJetAlgebra.totalDerivative i u) =
      ∑ j, c g i j • ScalarJetAlgebra.totalDerivative j (rho g u))
    (hE : ∀ g s, rho g (p.scalarEuler s) ∈ Submodule.span ℂ (Set.range p.scalarEuler)) : Bosonic B I H :=
  ⟨p,rho,p.scalar_stable_of_euler_span rho hM c hD hE⟩

variable (M : Bosonic B I H)
def input := M.density.scalarInput M.action M.stable
def presentation := M.density.scalarAllOrderPresentation M.action M.stable
abbrev Coordinates := M.presentation.rows
def equivalence : M.input.Coefficient ≃ₗ[ℂ] M.Coordinates := M.presentation.equivalence
def evaluate (q : M.Coordinates) : Scalar B I →ₗ[ℂ] ℂ := M.presentation.assemble q.val
theorem evaluate_encode (f : M.input.Coefficient) (u : Scalar B I) :
    M.evaluate (M.equivalence f) u = f.val u :=
  congrArg (fun f : M.input.Coefficient => f.val u) (M.equivalence.symm_apply_apply f)
theorem target_values_iff {T : Type*} (v : T → Scalar B I) (a : T → ℂ) :
    (∃ f : M.input.Coefficient, ∀ t, f.val (v t) = a t) ↔
    ∃ q : M.Coordinates, ∀ t, M.evaluate q (v t) = a t := M.presentation.target_values_iff v a
theorem reconstruction (f : M.input.Coefficient) (u : Scalar B I) :
    f.val u = (M.presentation.basis.repr u).sum (fun i a => a*(M.equivalence f).val i) :=
  M.presentation.reconstruction f u
theorem prescribed_iff (c : LocalPolynomial.Expr.ScalarMonomial B I → ℂ) :
    (∃ f : M.input.Coefficient, ∀ i, f.val (M.presentation.basis i) = c i) ↔
      c ∈ M.Coordinates := M.presentation.prescribed_iff c
theorem forbidden_iff : DerivativeProhibition.Forbids M.input ↔
    SelectionCriteria.Forbidden M.Coordinates := M.presentation.forbidden_iff
theorem allowed_iff : DerivativeProhibition.Allows M.input ↔
    SelectionCriteria.Allowed M.Coordinates := M.presentation.allowed_iff
def selected (V : Submodule ℂ (Scalar B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.input.select V hV
def selectedPresentation (V : Submodule ℂ (Scalar B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.presentation.canonicalSelectedPresentation V hV
def selectedEquivalence (V : Submodule ℂ (Scalar B I)) (hV : ∀ g, V ≤ V.comap (M.action g)) :=
  M.presentation.canonicalSelectedEquivalence V hV
end Bosonic
end
end Math.LagrangianModel
