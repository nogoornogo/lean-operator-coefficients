import Math.RepresentationTheory.Jets.DerivativeInterface
import Math.RepresentationTheory.Invariants.TwoSidedCovariance

/-! Changes of source presentation and of equation generators.
The complete relation module and the action are transported together. -/
namespace Math.InputPresentation
set_option autoImplicit false
noncomputable section
open Representation

variable {H U V : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]
  (P : DerivativeInterface.Input H U) (Q : DerivativeInterface.Input H V)
  (e : Representation.Equiv P.action Q.action)
  (h : P.relations.map e.toLinearEquiv.toLinearMap = Q.relations)

def source : P.Source ≃ₗ[ℂ] Q.Source :=
  Submodule.Quotient.equiv P.relations Q.relations e.toLinearEquiv h

@[simp] theorem projection (u : U) :
    source P Q e h (P.projection u) = Q.projection (e u) := rfl

def coefficients : P.Coefficient ≃ₗ[ℂ] Q.Coefficient where
  toFun f := ⟨InvariantCoefficientTransport.alongEquiv e f.val, by
    intro v hv
    rw [← h] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    change f.val (e.toLinearEquiv.symm (e.toLinearEquiv u)) = 0
    rw [e.toLinearEquiv.symm_apply_apply]
    exact f.property hu⟩
  invFun f := ⟨(InvariantCoefficientTransport.alongEquiv e).symm f.val, by
    intro u hu
    change f.val (e u) = 0
    apply f.property
    rw [← h]
    exact ⟨u,hu,rfl⟩⟩
  left_inv f := Subtype.ext ((InvariantCoefficientTransport.alongEquiv e).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((InvariantCoefficientTransport.alongEquiv e).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((InvariantCoefficientTransport.alongEquiv e).map_add f.val g.val)
  map_smul' z f := Subtype.ext ((InvariantCoefficientTransport.alongEquiv e).map_smul z f.val)

@[simp] theorem evaluation (f : P.Coefficient) (u : U) :
    (coefficients P Q e h f).val (e u) = f.val u :=
  congrArg f.val (e.toLinearEquiv.symm_apply_apply u)

theorem quotient_evaluation (f : P.Coefficient) (x : P.Source) :
    Q.coefficientEquiv (coefficients P Q e h f) (source P Q e h x) =
      P.coefficientEquiv f x := by
  obtain ⟨u,rfl⟩ := P.relations.mkQ_surjective x
  exact evaluation P Q e h f u

theorem inverse (f : P.Coefficient) :
    (coefficients P Q e h).symm (coefficients P Q e h f) = f :=
  (coefficients P Q e h).symm_apply_apply f

theorem nonzero_iff (f : P.Coefficient) : coefficients P Q e h f ≠ 0 ↔ f ≠ 0 :=
  (coefficients P Q e h).map_ne_zero_iff

/-- Any linear basis/relabel map is allowed when its action is transported. -/
def reexpress (b : U ≃ₗ[ℂ] V) : DerivativeInterface.Input H V where
  action := b.conjRingEquiv.toMonoidHom.comp P.action
  relations := P.relations.map b.toLinearMap
  stable g := by
    rintro _ ⟨u,hu,rfl⟩
    refine ⟨P.action g u,P.stable g hu,?_⟩
    change b (P.action g u) = b (P.action g (b.symm (b u)))
    rw [b.symm_apply_apply]

def reexpression (b : U ≃ₗ[ℂ] V) : Representation.Equiv P.action (reexpress P b).action :=
  Representation.Equiv.mk b (by
    intro g
    ext u
    change b (P.action g u) = b (P.action g (b.symm (b u)))
    rw [b.symm_apply_apply])

def reexpressCoefficients (b : U ≃ₗ[ℂ] V) :
    P.Coefficient ≃ₗ[ℂ] (reexpress P b).Coefficient :=
  coefficients P (reexpress P b) (reexpression P b) rfl

theorem reexpress_evaluation (b : U ≃ₗ[ℂ] V) (f : P.Coefficient) (u : U) :
    (reexpressCoefficients P b f).val (b u) = f.val u :=
  evaluation P (reexpress P b) (reexpression P b) rfl f u

section Seeds
variable {A I J : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A) (R : Set A)

theorem scaled_span (c : ℂ) (hc : c ≠ 0) :
    Submodule.span ℂ ((fun p : A => c • p) '' R) = Submodule.span ℂ R := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hp)
  · apply Submodule.span_le.mpr
    intro p hp
    have hm := Submodule.smul_mem (Submodule.span ℂ ((fun p : A => c • p) '' R))
      c⁻¹ (Submodule.subset_span ⟨p,hp,rfl⟩)
    simpa only [SetLike.mem_coe,smul_smul,inv_mul_cancel₀ hc,one_smul] using hm

theorem scaled_relations (c : ℂ) (hc : c ≠ 0) :
    TwoSidedDifferential.relations D ((fun p : A => c • p) '' R) =
      TwoSidedDifferential.relations D R :=
  TwoSidedDifferential.relations_eq_of_span D (scaled_span R c hc)

theorem scaled_combined (c : ℂ) (hc : c ≠ 0) :
    TwoSidedDifferential.combined D ((fun p : A => c • p) '' R) =
      TwoSidedDifferential.combined D R := by
  unfold TwoSidedDifferential.combined
  rw [scaled_relations D R c hc]

/-- An invertible elementary row operation, including derivative descendants. -/
theorem recombined_relations [DecidableEq J] (r : J → A) {i j : J} (hij : i ≠ j) (c : ℂ) :
    TwoSidedDifferential.relations D (Set.range (Function.update r j (r j+c • r i))) =
      TwoSidedDifferential.relations D (Set.range r) :=
  TwoSidedDifferential.relations_eq_of_span D (Submodule.span_range_update_add_smul hij r c)

theorem recombined_combined [DecidableEq J] (r : J → A) {i j : J} (hij : i ≠ j) (c : ℂ) :
    TwoSidedDifferential.combined D (Set.range (Function.update r j (r j+c • r i))) =
      TwoSidedDifferential.combined D (Set.range r) := by
  unfold TwoSidedDifferential.combined
  rw [recombined_relations D r hij c]
end Seeds
end
end Math.InputPresentation
