import Math.RepresentationTheory.Spurions.LocalSpurionEvaluation
import Math.RepresentationTheory.Jets.JetEquationComparison
import Math.Algebra.Jets.MixedJetFinite

/-! Finite-group spurion evaluation on actual fixed jet quotients. Internal
actions and local direction actions are combined before taking relations. -/
namespace Math.JetSpurionEvaluation
set_option autoImplicit false
noncomputable section
open Representation JetDirections PolynomialCovariantEvaluation

variable {L H S F B I T : Type*} [Group L] [Group H] [Fintype I]
  (σ : Representation ℂ L (Direction I))

def direction : Representation ℂ (L × H) (Direction I) := σ.comp (MonoidHom.fst L H)
def internal (ρ : Representation ℂ H (JetLinear.Field S)) :
    Representation ℂ (L × H) (JetLinear.Field S) := ρ.comp (MonoidHom.snd L H)

section Scalar
variable (q : Symbols I) (ρ : Representation ℂ H (JetLinear.Field S))
  (hq : ∀ g, symbolMap (σ g) q = q) (n d : ℕ)

omit [Fintype I] in
include hq in
theorem equation_invariant (g : L × H) : symbolMap (direction σ g) q = q := hq g.1

abbrev ScalarSource := JetEquation.grade S q n (d + 1) ⧸ JetEquation.shellRelations q n d

def scalarAction : Representation ℂ (L × H) (ScalarSource (S := S) q n d) :=
  JetEquation.shellQuotientAction q (internal (L := L) ρ) (direction σ)
    (equation_invariant σ q hq) n d

def scalarSourceEquiv := JetEquation.combinedRepresentationEquiv q
  (internal (L := L) ρ) (direction σ) (equation_invariant σ q hq) n d

variable [Finite S] [Fintype H] [Fintype T]
  (a : Representation ℂ H (T → ℂ)) (s : T → ℂ)

abbrev ScalarCoefficients := LocalSpurionEvaluation.Coefficients (scalarAction σ q ρ hq n d) a s
def scalarCoefficientEquiv := LocalSpurionEvaluation.coefficientEquiv (scalarAction σ q ρ hq n d) a s
def scalarEvaluation (b : ℕ) := LocalSpurionEvaluation.evaluation (scalarAction σ q ρ hq n d) a s b

theorem scalar_surjective : Function.Surjective (scalarEvaluation σ q ρ hq n d a s (orbitSize a s - 1)) :=
  LocalSpurionEvaluation.evaluation_surjective (scalarAction σ q ρ hq n d) a s

theorem scalar_card_surjective :
    Function.Surjective (scalarEvaluation σ q ρ hq n d a s (Fintype.card H - 1)) :=
  LocalSpurionEvaluation.card_evaluation_surjective (scalarAction σ q ρ hq n d) a s

theorem scalar_nonzero_iff : (∃ f : ScalarCoefficients σ q ρ hq n d a s, f ≠ 0) ↔
    ∃ p, scalarEvaluation σ q ρ hq n d a s (orbitSize a s - 1) p ≠ 0 :=
  LocalSpurionEvaluation.nonzero_iff (scalarAction σ q ρ hq n d) a s

omit [Fintype H] [Fintype T] in
/-- Evaluation on the original off-shell scalar representative. -/
theorem scalar_evaluation_off (b : ℕ)
    (p : boundedCovariants a (LocalSpurionEvaluation.dualAction (scalarAction σ q ρ hq n d)) b)
    (u : ScalarJetAlgebra.grade (S := S) (I := I) n (d + 1)) :
    (scalarEvaluation σ q ρ hq n d a s b p).val (JetEquation.combinedProjection q n d u) =
      (LocalSpurionEvaluation.coordinates (scalarAction σ q ρ hq n d)).symm (evaluate s p.val.val)
        ((LocalSpurionEvaluation.relations (scalarAction σ q ρ hq n d)).mkQ
          (JetEquation.combinedProjection q n d u)) := rfl

omit [Finite S] [Fintype H] [Fintype T] in
/-- Pullback loses no coefficient: the actual EOM/IBP projection is onto. -/
theorem scalar_pullback_injective : Function.Injective
    (fun f : ScalarCoefficients σ q ρ hq n d a s =>
      f.val.toLinearMap.comp (JetEquation.combinedProjection q n d)) := by
  intro f g he
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u, rfl⟩ := JetEquation.combinedProjection_surjective q n d u
  exact LinearMap.congr_fun he u
end Scalar

section Mixed
variable (ρF : Representation ℂ H (JetLinear.Field F))
  (ρB : Representation ℂ H (JetLinear.Field B)) (n m d : ℕ)

@[reducible] local instance (n m d : ℕ) : AddCommGroup (MixedJetAlgebra.grade F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (MixedJetAlgebra.grade F B I n m d) := inferInstance

abbrev mixedRelations := GradedJetIBP.relations (V := fun e => MixedJetAlgebra.grade F B I n m e)
  (DirectionalJetIBP.mixedDerivatives (F := F) (B := B) (I := I) n m) d

theorem mixed_stable : ∀ g : L × H, mixedRelations (F := F) (B := B) (I := I) n m d ≤
    (mixedRelations n m d).comap
      (DirectionalJetIBP.mixedAction (direction σ) (internal (L := L) ρF)
        (internal (L := L) ρB) n m (d + 1) g) := by
  intro g u hu
  obtain ⟨c, rfl⟩ := hu
  induction c using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add c e hc he => simpa only [map_add] using Submodule.add_mem _ hc he
  | single i p =>
    rw [GradedJetIBP.divergence_single]
    change DirectionalJetIBP.mixedAction (direction σ) (internal (L := L) ρF)
      (internal (L := L) ρB) n m (d + 1) g (MixedJetAlgebra.derivative i n m d p) ∈ mixedRelations (F := F) (B := B) (I := I) n m d
    rw [DirectionalJetIBP.mixed_covariance]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (GradedJetIBP.derivative_mem (DirectionalJetIBP.mixedDerivatives
        (F := F) (B := B) (I := I) n m) d j _))

abbrev MixedSource := MixedJetAlgebra.grade F B I n m (d + 1) ⧸ mixedRelations n m d

def mixedAction : Representation ℂ (L × H) (MixedSource (F := F) (B := B) (I := I) n m d) :=
  (DirectionalJetIBP.mixedAction (direction σ) (internal (L := L) ρF)
    (internal (L := L) ρB) n m (d + 1)).quotient (mixedRelations n m d) (mixed_stable σ ρF ρB n m d)

def mixedSourceEquiv := DirectionalJetIBP.mixedSourceEquiv (direction σ)
  (internal (L := L) ρF) (internal (L := L) ρB) n m (d + 1)

variable [Finite F] [Finite B] [Fintype H] [Fintype T]
  (a : Representation ℂ H (T → ℂ)) (s : T → ℂ)

abbrev MixedCoefficients := LocalSpurionEvaluation.Coefficients (mixedAction σ ρF ρB n m d) a s
def mixedCoefficientEquiv := LocalSpurionEvaluation.coefficientEquiv (mixedAction σ ρF ρB n m d) a s
def mixedEvaluation (b : ℕ) := LocalSpurionEvaluation.evaluation (mixedAction σ ρF ρB n m d) a s b

theorem mixed_surjective :
    Function.Surjective (mixedEvaluation σ ρF ρB n m d a s (orbitSize a s - 1)) :=
  LocalSpurionEvaluation.evaluation_surjective (mixedAction σ ρF ρB n m d) a s

theorem mixed_card_surjective :
    Function.Surjective (mixedEvaluation σ ρF ρB n m d a s (Fintype.card H - 1)) :=
  LocalSpurionEvaluation.card_evaluation_surjective (mixedAction σ ρF ρB n m d) a s

theorem mixed_nonzero_iff : (∃ f : MixedCoefficients σ ρF ρB n m d a s, f ≠ 0) ↔
    ∃ p, mixedEvaluation σ ρF ρB n m d a s (orbitSize a s - 1) p ≠ 0 :=
  LocalSpurionEvaluation.nonzero_iff (mixedAction σ ρF ρB n m d) a s

/-- The exterior/symmetric tensor presentation maps to the actual IBP quotient. -/
def mixedProjection := (mixedRelations (F := F) (B := B) (I := I) n m d).mkQ.comp
  (mixedSourceEquiv σ ρF ρB n m d).toLinearEquiv.toLinearMap

omit [Fintype I] [Finite F] [Finite B] [Fintype H] in
theorem mixedProjection_surjective : Function.Surjective (mixedProjection σ ρF ρB n m d) :=
  (mixedRelations n m d).mkQ_surjective.comp (mixedSourceEquiv σ ρF ρB n m d).toLinearEquiv.surjective

omit [Fintype H] [Fintype T] in
theorem mixed_evaluation_tensor (b : ℕ)
    (p : boundedCovariants a (LocalSpurionEvaluation.dualAction (mixedAction σ ρF ρB n m d)) b)
    (u : MixedJetSource.sourceGrade F B I n m (d + 1)) :
    (mixedEvaluation σ ρF ρB n m d a s b p).val (mixedProjection σ ρF ρB n m d u) =
      (LocalSpurionEvaluation.coordinates (mixedAction σ ρF ρB n m d)).symm (evaluate s p.val.val)
        ((LocalSpurionEvaluation.relations (mixedAction σ ρF ρB n m d)).mkQ
          (mixedProjection σ ρF ρB n m d u)) := rfl

omit [Finite F] [Finite B] [Fintype H] [Fintype T] in
theorem mixed_pullback_injective : Function.Injective
    (fun f : MixedCoefficients σ ρF ρB n m d a s =>
      f.val.toLinearMap.comp (mixedProjection σ ρF ρB n m d)) := by
  intro f g he
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u, rfl⟩ := mixedProjection_surjective σ ρF ρB n m d u
  exact LinearMap.congr_fun he u
end Mixed

end
end Math.JetSpurionEvaluation
