import Math.LinearAlgebra.Constructions.EigenbasisTrace
import GUT.SU6.Characters.VirtualRestriction

open Math

/-!
# Weight-theory interface for the actual Laurent provider

This file isolates the Lie-theoretic input needed to construct Laurent
polynomials for all source representations.

For an actual finite-dimensional SU(6) representation, torus weight theory
should produce a finite Laurent character: a finite list of weights with
integer multiplicities whose evaluation on the flipped torus is the restricted
character.  Once those finite weight characters are supplied for all actual
representations, and once the diagonal flipped-torus evaluator is known to be
faithful, the `ActualLaurentModelProvider` used by the virtual obstruction is
constructed here.  The function-level no-uplift theorem does not depend on
this global provider.
-/

namespace GUT
namespace WeightTheory

open VirtualRestriction
open scoped BigOperators

noncomputable section

abbrev FlippedDiagonalSU6Point := FlippedTorus.FlippedDiagonalSU6Point
abbrev ActualSU6Representation := VirtualRestriction.ActualSU6Representation

def diagonalLaurentEval
    (p : Flipped.Poly) (t : FlippedDiagonalSU6Point) : ℂ :=
  Flipped.Poly.eval p t.toAlgebraicTorusPoint

abbrev DiagonalLaurentFaithful : Prop :=
  ∀ p q : Flipped.Poly,
    (∀ t : FlippedDiagonalSU6Point,
      diagonalLaurentEval p t = diagonalLaurentEval q t) -> p = q

def commonLaurentEvaluatorOfFaithful
    (hfaithful : DiagonalLaurentFaithful) :
    CommonLaurentEvaluator where
  eval := diagonalLaurentEval
  eval_zero := by
    intro t
    exact Flipped.Poly.eval_zero t.toAlgebraicTorusPoint
  eval_add := by
    intro p q t
    exact Flipped.Poly.eval_add p q t.toAlgebraicTorusPoint
  eval_zscale := by
    intro n p t
    exact Flipped.Poly.eval_zscale n p t.toAlgebraicTorusPoint
  eval_swap36 := by
    intro p t
    unfold diagonalLaurentEval
    rw [Flipped.Poly.eval_swap36,
      ← FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36 t]
  faithful := hfaithful

structure ActualTorusWeightCharacter
    (R : ActualSU6Representation) where
  weights : Flipped.RawCharacter Flipped.Exp
  evaluates_restrictedCharacter :
    ∀ t : FlippedDiagonalSU6Point,
      diagonalLaurentEval (Flipped.RawCharacter.toPoly weights) t =
        R.restrictedCharacter t

namespace ActualTorusWeightCharacter

def poly {R : ActualSU6Representation}
    (χ : ActualTorusWeightCharacter R) : Flipped.Poly :=
  Flipped.RawCharacter.toPoly χ.weights

theorem poly_evaluates {R : ActualSU6Representation}
    (χ : ActualTorusWeightCharacter R) (t : FlippedDiagonalSU6Point) :
    diagonalLaurentEval χ.poly t = R.restrictedCharacter t :=
  χ.evaluates_restrictedCharacter t

end ActualTorusWeightCharacter

structure SU6TorusWeightTheory where
  character : ∀ R : ActualSU6Representation, ActualTorusWeightCharacter R

theorem list_sum_toList_map
    {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (f : ι -> M) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  rw [← Multiset.sum_coe (s.toList.map f)]
  change ((s.toList : Multiset ι).map f).sum = ∑ i ∈ s, f i
  rw [Finset.coe_toList]
  exact (Finset.sum_mk s.val s.nodup f).symm

def rawCharacterOfWeights
    {ι : Type*} [Fintype ι]
    (weight : ι -> Flipped.Exp) : Flipped.RawCharacter Flipped.Exp :=
  (Finset.univ : Finset ι).toList.map
    (fun i => { exp := weight i, coeff := 1 })

theorem rawCharacterOfWeights_eval
    {ι : Type*} [Fintype ι]
    (weight : ι -> Flipped.Exp) (x : Flipped.AlgebraicTorusPoint) :
    Flipped.RawCharacter.eval (rawCharacterOfWeights weight) x =
      ∑ i : ι, Flipped.Exp.eval (weight i) x := by
  rw [rawCharacterOfWeights, Flipped.RawCharacter.eval_mapWeights_one]
  exact list_sum_toList_map (Finset.univ : Finset ι)
    (fun i => Flipped.Exp.eval (weight i) x)

structure TorusEigenbasis (R : ActualSU6Representation) where
  ι : Type
  [instFintype : Fintype ι]
  [instDecidableEq : DecidableEq ι]
  basis : Module.Basis ι ℂ R.V
  weight : ι -> Flipped.Exp
  action_on_basis :
    ∀ (t : FlippedDiagonalSU6Point) (i : ι),
      R.rho t.toDiagonal.toSU6 (basis i) =
        Flipped.Exp.eval (weight i) t.toAlgebraicTorusPoint • basis i

attribute [instance] TorusEigenbasis.instFintype
attribute [instance] TorusEigenbasis.instDecidableEq

namespace TorusEigenbasis

def rawCharacter {R : ActualSU6Representation}
    (D : TorusEigenbasis R) : Flipped.RawCharacter Flipped.Exp :=
  rawCharacterOfWeights D.weight

theorem restrictedCharacter_eq_sum
    {R : ActualSU6Representation}
    (D : TorusEigenbasis R) (t : FlippedDiagonalSU6Point) :
    R.restrictedCharacter t =
      ∑ i : D.ι, Flipped.Exp.eval (D.weight i) t.toAlgebraicTorusPoint := by
  simpa [ActualSU6Representation.restrictedCharacter,
    FlippedTorus.FlippedDiagonalSU6Point.restrictedCharacter,
    ActualRestriction.restrictedCharacter, Representation.character]
    using Math.WeightTheory.trace_eq_sum_of_basis_eigen D.basis
      (R.rho t.toDiagonal.toSU6)
      (fun i => Flipped.Exp.eval (D.weight i) t.toAlgebraicTorusPoint)
      (D.action_on_basis t)

def toActualTorusWeightCharacter
    {R : ActualSU6Representation}
    (D : TorusEigenbasis R) : ActualTorusWeightCharacter R where
  weights := D.rawCharacter
  evaluates_restrictedCharacter := by
    intro t
    rw [diagonalLaurentEval, Flipped.RawCharacter.eval_toPoly,
      rawCharacter, rawCharacterOfWeights_eval]
    exact (D.restrictedCharacter_eq_sum t).symm

end TorusEigenbasis

structure SU6TorusEigenbasisTheory where
  eigenbasis : ∀ R : ActualSU6Representation, TorusEigenbasis R

def torusWeightTheoryOfEigenbasisTheory
    (T : SU6TorusEigenbasisTheory) : SU6TorusWeightTheory where
  character := fun R => (T.eigenbasis R).toActualTorusWeightCharacter

def actualLaurentModelProviderOfEigenbasisTheory
    (hfaithful : DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory) :
    ActualLaurentModelProvider (commonLaurentEvaluatorOfFaithful hfaithful) where
  poly := fun R => ((T.eigenbasis R).toActualTorusWeightCharacter).poly
  evaluates_rep := by
    intro R t
    exact ((T.eigenbasis R).toActualTorusWeightCharacter).poly_evaluates t

theorem finiteVirtual_has_laurent_model_of_eigenbasisTheory
    (hfaithful : DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory)
    (χ : FiniteVirtualSU6Representation) :
    ∃ M : VirtualLaurentModel χ,
      M.poly =
          FiniteVirtualSU6Representation.polyOfProvider
            (actualLaurentModelProviderOfEigenbasisTheory hfaithful T) χ ∧
        Flipped.swap36 M.poly = M.poly := by
  exact
    FiniteVirtualSU6Representation.restrictedCharacter_has_faithful_swapCompatible_laurent_model
      (actualLaurentModelProviderOfEigenbasisTheory hfaithful T) χ

theorem no_flippedSM_uplift_of_eigenbasisTheory
    (hfaithful : DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      FiniteVirtualSU6Representation.polyOfProvider
        (actualLaurentModelProviderOfEigenbasisTheory hfaithful T) χ =
          Flipped.flippedSMCharacter := by
  exact
    FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider
      (actualLaurentModelProviderOfEigenbasisTheory hfaithful T)

theorem no_flippedSMExplicit_uplift_of_eigenbasisTheory
    (hfaithful : DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      FiniteVirtualSU6Representation.polyOfProvider
        (actualLaurentModelProviderOfEigenbasisTheory hfaithful T) χ =
          Flipped.flippedSMCharacterExplicit := by
  exact
    FiniteVirtualSU6Representation.no_flippedSMExplicit_uplift_of_actual_provider
      (actualLaurentModelProviderOfEigenbasisTheory hfaithful T)

def actualLaurentModelProviderOfWeightTheory
    (hfaithful : DiagonalLaurentFaithful)
    (W : SU6TorusWeightTheory) :
    ActualLaurentModelProvider (commonLaurentEvaluatorOfFaithful hfaithful) where
  poly := fun R => (W.character R).poly
  evaluates_rep := by
    intro R t
    exact (W.character R).poly_evaluates t

theorem finiteVirtual_has_laurent_model_of_weight_theory
    (hfaithful : DiagonalLaurentFaithful)
    (W : SU6TorusWeightTheory)
    (χ : FiniteVirtualSU6Representation) :
    ∃ M : VirtualLaurentModel χ,
      M.poly =
          FiniteVirtualSU6Representation.polyOfProvider
            (actualLaurentModelProviderOfWeightTheory hfaithful W) χ ∧
        Flipped.swap36 M.poly = M.poly := by
  exact
    FiniteVirtualSU6Representation.restrictedCharacter_has_faithful_swapCompatible_laurent_model
      (actualLaurentModelProviderOfWeightTheory hfaithful W) χ

theorem finiteVirtual_poly_swap36_fixed_of_weight_theory
    (hfaithful : DiagonalLaurentFaithful)
    (W : SU6TorusWeightTheory)
    (χ : FiniteVirtualSU6Representation) :
    Flipped.swap36
        (FiniteVirtualSU6Representation.polyOfProvider
          (actualLaurentModelProviderOfWeightTheory hfaithful W) χ) =
      FiniteVirtualSU6Representation.polyOfProvider
        (actualLaurentModelProviderOfWeightTheory hfaithful W) χ := by
  exact
    FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed
      (actualLaurentModelProviderOfWeightTheory hfaithful W) χ

theorem no_flippedSM_uplift_of_weight_theory
    (hfaithful : DiagonalLaurentFaithful)
    (W : SU6TorusWeightTheory) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      FiniteVirtualSU6Representation.polyOfProvider
        (actualLaurentModelProviderOfWeightTheory hfaithful W) χ =
          Flipped.flippedSMCharacter := by
  exact
    FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider
      (actualLaurentModelProviderOfWeightTheory hfaithful W)

theorem no_flippedSMExplicit_uplift_of_weight_theory
    (hfaithful : DiagonalLaurentFaithful)
    (W : SU6TorusWeightTheory) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      FiniteVirtualSU6Representation.polyOfProvider
        (actualLaurentModelProviderOfWeightTheory hfaithful W) χ =
          Flipped.flippedSMCharacterExplicit := by
  exact
    FiniteVirtualSU6Representation.no_flippedSMExplicit_uplift_of_actual_provider
      (actualLaurentModelProviderOfWeightTheory hfaithful W)

end

end WeightTheory
end GUT
