import GUT.SU6.SelectionRules.FlippedBranch.FlippedTorus

open Math

/-!
# Finite virtual SU(6) restricted characters

This file formalizes the finite-virtual step.  A virtual representation is
modeled as a finite integer-linear combination of actual finite-dimensional
complex representations of `SU(6)`.

The kernel-checked result is that the restricted virtual character is fixed by
the concrete `(3 6)` Weyl action.  It also proves that, once the actual
summands are supplied with Laurent polynomials in one common faithful,
swap-compatible evaluator, the finite virtual combination has a faithful
Laurent-polynomial model.

For the source-polynomial realization route, the additional mathematical bridge
is the existence of such actual summand Laurent polynomials and the faithful
evaluator from genuine SU(6) torus character theory.  The later function-level
no-uplift theorem in `GUT.NormalizedLaurent` does not require source-side
Laurent models.
-/

namespace GUT
namespace VirtualRestriction

open Representation

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev DiagonalSU6Point := FlippedTorus.FlippedDiagonalSU6Point

structure ActualSU6Representation where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  rho : Representation ℂ SU6 V

attribute [instance] ActualSU6Representation.instAddCommGroup
attribute [instance] ActualSU6Representation.instModule
attribute [instance] ActualSU6Representation.instFiniteDimensional

namespace ActualSU6Representation

def restrictedCharacter (R : ActualSU6Representation) (t : DiagonalSU6Point) : ℂ :=
  FlippedTorus.FlippedDiagonalSU6Point.restrictedCharacter R.rho t

theorem restrictedCharacter_swap36_fixed
    (R : ActualSU6Representation) (t : DiagonalSU6Point) :
    R.restrictedCharacter (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      R.restrictedCharacter t := by
  exact FlippedTorus.FlippedDiagonalSU6Point.restrictedCharacter_swap36_fixed R.rho t

end ActualSU6Representation

structure VirtualSummand where
  coeff : Int
  rep : ActualSU6Representation

namespace VirtualSummand

def restrictedCharacter (s : VirtualSummand) (t : DiagonalSU6Point) : ℂ :=
  (s.coeff : ℂ) * s.rep.restrictedCharacter t

theorem restrictedCharacter_swap36_fixed
    (s : VirtualSummand) (t : DiagonalSU6Point) :
    s.restrictedCharacter (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      s.restrictedCharacter t := by
  simp [restrictedCharacter, s.rep.restrictedCharacter_swap36_fixed t]

end VirtualSummand

abbrev FiniteVirtualSU6Representation := List VirtualSummand

namespace FiniteVirtualSU6Representation

def restrictedCharacter :
    FiniteVirtualSU6Representation -> DiagonalSU6Point -> ℂ
  | [], _ => 0
  | s :: ss, t => s.restrictedCharacter t + restrictedCharacter ss t

/-- Convert the legacy finite presentation to coefficients of actual
mathlib representations, combining repeated identical objects. -/
def toCharacterCoefficients : FiniteVirtualSU6Representation → FDRep ℂ SU6 →₀ ℤ
  | [] => 0
  | s :: ss => Finsupp.single (FDRep.of s.rep.rho) s.coeff + toCharacterCoefficients ss

/-- The generic finite-virtual restriction is exactly the existing character. -/
theorem virtualRestriction_eq_restrictedCharacter
    (χ : FiniteVirtualSU6Representation) (t : DiagonalSU6Point) :
    CharacterRestriction.virtualRestriction (fun t : DiagonalSU6Point => t.toDiagonal.toSU6)
      (toCharacterCoefficients χ) t = restrictedCharacter χ t := by
  change CharacterRestriction.virtualCharacter (fun R : FDRep ℂ SU6 => R.ρ)
    (toCharacterCoefficients χ) t.toDiagonal.toSU6 = restrictedCharacter χ t
  induction χ with
  | nil => simp [toCharacterCoefficients, restrictedCharacter]
  | cons s ss ih =>
      simp [toCharacterCoefficients, restrictedCharacter, ih,
        VirtualSummand.restrictedCharacter, ActualSU6Representation.restrictedCharacter,
        FlippedTorus.FlippedDiagonalSU6Point.restrictedCharacter,
        ActualRestriction.restrictedCharacter, zsmul_eq_mul]

theorem restrictedCharacter_swap36_fixed
    (χ : FiniteVirtualSU6Representation) (t : DiagonalSU6Point) :
    restrictedCharacter χ (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) =
      restrictedCharacter χ t := by
  rw [← virtualRestriction_eq_restrictedCharacter,
    ← virtualRestriction_eq_restrictedCharacter]
  exact CharacterRestriction.virtualCharacter_restriction_invariant
    (fun R : FDRep ℂ SU6 => R.ρ) (toCharacterCoefficients χ)
    (fun t : DiagonalSU6Point => t.toDiagonal.toSU6)
    FlippedTorus.FlippedDiagonalSU6Point.swap36 WeylMatrix.signedSwap36SU
    (fun t => ActualRestriction.DiagonalSU6Point.toSU6_swap36_eq_conj t.toDiagonal) t

end FiniteVirtualSU6Representation

structure CommonLaurentEvaluator where
  eval : Flipped.Poly -> DiagonalSU6Point -> ℂ
  eval_zero : ∀ t, eval 0 t = 0
  eval_add : ∀ p q t, eval (p + q) t = eval p t + eval q t
  eval_zscale : ∀ n p t, eval (Flipped.Poly.zscale n p) t = (n : ℂ) * eval p t
  eval_swap36 :
    ∀ p t, eval (Flipped.swap36 p) t =
      eval p (FlippedTorus.FlippedDiagonalSU6Point.swap36 t)
  faithful :
    ∀ p q, (∀ t, eval p t = eval q t) -> p = q

structure ModeledVirtualSummand (E : CommonLaurentEvaluator) where
  coeff : Int
  rep : ActualSU6Representation
  poly : Flipped.Poly
  evaluates_rep :
    ∀ t, E.eval poly t = rep.restrictedCharacter t

namespace ModeledVirtualSummand

def toVirtualSummand {E : CommonLaurentEvaluator}
    (s : ModeledVirtualSummand E) : VirtualSummand :=
  { coeff := s.coeff, rep := s.rep }

def weightedPoly {E : CommonLaurentEvaluator}
    (s : ModeledVirtualSummand E) : Flipped.Poly :=
  Flipped.Poly.zscale s.coeff s.poly

theorem weightedPoly_evaluates {E : CommonLaurentEvaluator}
    (s : ModeledVirtualSummand E) (t : DiagonalSU6Point) :
    E.eval s.weightedPoly t = s.toVirtualSummand.restrictedCharacter t := by
  simp [weightedPoly, toVirtualSummand, VirtualSummand.restrictedCharacter,
    E.eval_zscale, s.evaluates_rep]

end ModeledVirtualSummand

abbrev ModeledFiniteVirtualSU6Representation
    (E : CommonLaurentEvaluator) := List (ModeledVirtualSummand E)

namespace ModeledFiniteVirtualSU6Representation

def toVirtual {E : CommonLaurentEvaluator} :
    ModeledFiniteVirtualSU6Representation E -> FiniteVirtualSU6Representation
  | [] => []
  | s :: ss => s.toVirtualSummand :: toVirtual ss

def poly {E : CommonLaurentEvaluator} :
    ModeledFiniteVirtualSU6Representation E -> Flipped.Poly
  | [] => 0
  | s :: ss => s.weightedPoly + poly ss

theorem poly_evaluates {E : CommonLaurentEvaluator}
    (χ : ModeledFiniteVirtualSU6Representation E) (t : DiagonalSU6Point) :
    E.eval (poly χ) t =
      FiniteVirtualSU6Representation.restrictedCharacter (toVirtual χ) t := by
  induction χ with
  | nil =>
      simp [poly, toVirtual, FiniteVirtualSU6Representation.restrictedCharacter,
        E.eval_zero]
  | cons s ss ih =>
      rw [poly, toVirtual, FiniteVirtualSU6Representation.restrictedCharacter,
        E.eval_add, s.weightedPoly_evaluates, ih]

end ModeledFiniteVirtualSU6Representation

structure VirtualLaurentModel
    (χ : FiniteVirtualSU6Representation) where
  poly : Flipped.Poly
  eval : Flipped.Poly -> DiagonalSU6Point -> ℂ
  evaluates_character :
    ∀ t, eval poly t = FiniteVirtualSU6Representation.restrictedCharacter χ t
  eval_swap36 :
    ∀ p t, eval (Flipped.swap36 p) t =
      eval p (FlippedTorus.FlippedDiagonalSU6Point.swap36 t)
  faithful :
    ∀ p q, (∀ t, eval p t = eval q t) -> p = q

namespace VirtualLaurentModel

theorem swap36_fixed
    {χ : FiniteVirtualSU6Representation}
    (M : VirtualLaurentModel χ) :
    Flipped.swap36 M.poly = M.poly := by
  apply M.faithful
  intro t
  rw [M.eval_swap36, M.evaluates_character, M.evaluates_character,
    FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed]

theorem poly_ne_flippedSMCharacter
    {χ : FiniteVirtualSU6Representation}
    (M : VirtualLaurentModel χ) :
    M.poly ≠ Flipped.flippedSMCharacter := by
  intro h
  have hfixed := M.swap36_fixed
  rw [h] at hfixed
  exact Flipped.swap36_flippedSM_ne hfixed

theorem poly_ne_flippedSMCharacterExplicit
    {χ : FiniteVirtualSU6Representation}
    (M : VirtualLaurentModel χ) :
    M.poly ≠ Flipped.flippedSMCharacterExplicit := by
  intro h
  have hfixed := M.swap36_fixed
  rw [h] at hfixed
  exact Flipped.swap36_flippedSMExplicit_ne hfixed

end VirtualLaurentModel

theorem modeledFiniteVirtual_has_laurent_model
    {E : CommonLaurentEvaluator}
    (χ : ModeledFiniteVirtualSU6Representation E) :
    ∃ M : VirtualLaurentModel
        (ModeledFiniteVirtualSU6Representation.toVirtual χ),
      M.poly = ModeledFiniteVirtualSU6Representation.poly χ := by
  refine ⟨{
    poly := ModeledFiniteVirtualSU6Representation.poly χ
    eval := E.eval
    evaluates_character :=
      ModeledFiniteVirtualSU6Representation.poly_evaluates χ
    eval_swap36 := E.eval_swap36
    faithful := E.faithful
  }, rfl⟩

theorem modeledFiniteVirtual_poly_swap36_fixed
    {E : CommonLaurentEvaluator}
    (χ : ModeledFiniteVirtualSU6Representation E) :
    Flipped.swap36 (ModeledFiniteVirtualSU6Representation.poly χ) =
      ModeledFiniteVirtualSU6Representation.poly χ := by
  rcases modeledFiniteVirtual_has_laurent_model χ with ⟨M, hM⟩
  rw [← hM]
  exact M.swap36_fixed

theorem modeledFiniteVirtual_poly_ne_flippedSMCharacter
    {E : CommonLaurentEvaluator}
    (χ : ModeledFiniteVirtualSU6Representation E) :
    ModeledFiniteVirtualSU6Representation.poly χ ≠ Flipped.flippedSMCharacter := by
  intro h
  have hfixed := modeledFiniteVirtual_poly_swap36_fixed χ
  rw [h] at hfixed
  exact Flipped.swap36_flippedSM_ne hfixed

theorem modeledFiniteVirtual_poly_ne_flippedSMCharacterExplicit
    {E : CommonLaurentEvaluator}
    (χ : ModeledFiniteVirtualSU6Representation E) :
    ModeledFiniteVirtualSU6Representation.poly χ ≠
      Flipped.flippedSMCharacterExplicit := by
  intro h
  have hfixed := modeledFiniteVirtual_poly_swap36_fixed χ
  rw [h] at hfixed
  exact Flipped.swap36_flippedSMExplicit_ne hfixed

structure ActualLaurentModelProvider (E : CommonLaurentEvaluator) where
  poly : ActualSU6Representation -> Flipped.Poly
  evaluates_rep :
    ∀ R t, E.eval (poly R) t = R.restrictedCharacter t

namespace FiniteVirtualSU6Representation

def modeledBy {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    FiniteVirtualSU6Representation -> ModeledFiniteVirtualSU6Representation E
  | [] => []
  | s :: ss =>
      { coeff := s.coeff
        rep := s.rep
        poly := P.poly s.rep
        evaluates_rep := P.evaluates_rep s.rep } :: modeledBy P ss

theorem modeledBy_toVirtual {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    ∀ χ : FiniteVirtualSU6Representation,
      ModeledFiniteVirtualSU6Representation.toVirtual (modeledBy P χ) = χ
  | [] => rfl
  | s :: ss => by
      simp [modeledBy, ModeledFiniteVirtualSU6Representation.toVirtual,
        modeledBy_toVirtual P ss, ModeledVirtualSummand.toVirtualSummand]

def polyOfProvider {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) : Flipped.Poly :=
  ModeledFiniteVirtualSU6Representation.poly (modeledBy P χ)

theorem has_laurent_model_of_actual_provider
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    ∃ M : VirtualLaurentModel χ, M.poly = polyOfProvider P χ := by
  refine ⟨{
    poly := polyOfProvider P χ
    eval := E.eval
    evaluates_character := ?_
    eval_swap36 := E.eval_swap36
    faithful := E.faithful
  }, rfl⟩
  intro t
  rw [polyOfProvider, ModeledFiniteVirtualSU6Representation.poly_evaluates,
    modeledBy_toVirtual P χ]

theorem restrictedCharacter_has_faithful_swapCompatible_laurent_model
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    ∃ M : VirtualLaurentModel χ,
      M.poly = polyOfProvider P χ ∧ Flipped.swap36 M.poly = M.poly := by
  rcases has_laurent_model_of_actual_provider P χ with ⟨M, hM⟩
  exact ⟨M, hM, M.swap36_fixed⟩

theorem polyOfProvider_swap36_fixed
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    Flipped.swap36 (polyOfProvider P χ) = polyOfProvider P χ := by
  rcases has_laurent_model_of_actual_provider P χ with ⟨M, hM⟩
  rw [← hM]
  exact M.swap36_fixed

theorem polyOfProvider_ne_flippedSMCharacter
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    polyOfProvider P χ ≠ Flipped.flippedSMCharacter := by
  intro h
  have hfixed := polyOfProvider_swap36_fixed P χ
  rw [h] at hfixed
  exact Flipped.swap36_flippedSM_ne hfixed

theorem polyOfProvider_ne_flippedSMCharacterExplicit
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    polyOfProvider P χ ≠ Flipped.flippedSMCharacterExplicit := by
  intro h
  have hfixed := polyOfProvider_swap36_fixed P χ
  rw [h] at hfixed
  exact Flipped.swap36_flippedSMExplicit_ne hfixed

theorem no_flippedSM_uplift_of_actual_provider
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      polyOfProvider P χ = Flipped.flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact polyOfProvider_ne_flippedSMCharacter P χ hχ

theorem no_flippedSMExplicit_uplift_of_actual_provider
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      polyOfProvider P χ = Flipped.flippedSMCharacterExplicit := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact polyOfProvider_ne_flippedSMCharacterExplicit P χ hχ

end FiniteVirtualSU6Representation

end

end VirtualRestriction
end GUT
