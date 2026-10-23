import Math.RepresentationTheory.Jets.JetInputAdapter

/-! A single mixed operator coefficient interface for every derivative degree,
including zero. Arbitrary direction actions are retained at degree zero. -/
namespace Math.MixedOperatorInput
set_option autoImplicit false
noncomputable section
open Representation JetLinear MixedJetSource
open scoped TensorProduct

variable {F B I H : Type*} [Fintype I] [Group H]
  (rhoF : Representation ℂ H (JetLinear.Field F))
  (rhoB : Representation ℂ H (JetLinear.Field B))
  (sigma : Representation ℂ H (JetDirections.Direction I))

abbrev Source (F B I : Type*) (n m d : ℕ) := MixedJetAlgebra.grade F B I n m d
@[reducible] local instance (n m d : ℕ) : AddCommGroup (Source F B I n m d) := inferInstance
@[reducible] local instance (n m d : ℕ) : Module ℂ (Source F B I n m d) := inferInstance
@[reducible] local instance (n m : ℕ) : AddCommGroup (Original F B n m) := inferInstance
@[reducible] local instance (n m : ℕ) : Module ℂ (Original F B n m) := inferInstance
@[reducible] local instance (n m : ℕ) : AddCommGroup (MixedJetSource.Source F B I n m) := inferInstance
@[reducible] local instance (n m : ℕ) : Module ℂ (MixedJetSource.Source F B I n m) := inferInstance

abbrev action (n m d : ℕ) := DirectionalJetIBP.mixedAction sigma rhoF rhoB n m d

def relations (n m : ℕ) : (d : ℕ) → Submodule ℂ (Source F B I n m d)
  | 0 => ⊥
  | d + 1 => JetInputAdapter.mixedRelations n m d

theorem stable (n m d : ℕ) : ∀ h, relations (F := F) (B := B) (I := I) n m d ≤
    (relations n m d).comap (action rhoF rhoB sigma n m d h) := by
  cases d with
  | zero => exact fun _ => bot_le
  | succ d =>
    exact CovariantJetIBP.stable _ sigma (action rhoF rhoB sigma n m)
      (fun h i d => DirectionalJetIBP.mixed_covariance sigma rhoF rhoB n m h i d) d

abbrev Coefficient (n m d : ℕ) := JetInputAdapter.Input (action rhoF rhoB sigma n m d)
  (trivial ℂ H ℂ) (relations (F := F) (B := B) (I := I) n m d)

abbrev residual (n m d : ℕ) := (action rhoF rhoB sigma n m d).quotient
  (relations n m d) (stable rhoF rhoB sigma n m d)

def coefficientEquiv (n m d : ℕ) : Coefficient rhoF rhoB sigma n m d ≃ₗ[ℂ]
    IntertwiningMap (residual rhoF rhoB sigma n m d) (trivial ℂ H ℂ) :=
  JetInputAdapter.equiv _ _ _ (stable rhoF rhoB sigma n m d)

@[simp] theorem extraction (n m d : ℕ) (f : Coefficient rhoF rhoB sigma n m d)
    (p : Source F B I n m d) : coefficientEquiv rhoF rhoB sigma n m d f
      ((relations n m d).mkQ p) = f.val p := rfl

@[simp] theorem reconstruction (n m d : ℕ)
    (f : IntertwiningMap (residual rhoF rhoB sigma n m d) (trivial ℂ H ℂ)) (p : Source F B I n m d) :
    ((coefficientEquiv rhoF rhoB sigma n m d).symm f).val p = f ((relations n m d).mkQ p) := rfl

theorem nonzero_iff (n m d : ℕ) : (∃ f : Coefficient rhoF rhoB sigma n m d, f ≠ 0) ↔
    ∃ f : IntertwiningMap (residual rhoF rhoB sigma n m d) (trivial ℂ H ℂ), f ≠ 0 :=
  JetInputAdapter.nonzero_iff _ _ _ _

omit [Fintype I] in
@[simp] theorem admissible_zero (n m : ℕ)
    (f : IntertwiningMap (action rhoF rhoB sigma n m 0) (trivial ℂ H ℂ)) :
    f ∈ Coefficient rhoF rhoB sigma n m 0 :=
  show (⊥ : Submodule ℂ (Source F B I n m 0)) ≤ f.toLinearMap.ker from bot_le

omit [Fintype I] in
theorem admissible_succ (n m d : ℕ)
    (f : IntertwiningMap (action rhoF rhoB sigma n m (d + 1)) (trivial ℂ H ℂ)) :
    f ∈ Coefficient rhoF rhoB sigma n m (d + 1) ↔
      ∀ i p, f (MixedJetAlgebra.derivative i n m d p) = 0 :=
  by
    change CovariantJetIBP.relations (DirectionalJetIBP.mixedDerivatives (I := I) n m) d ≤ f.toLinearMap.ker ↔ _
    exact CovariantJetIBP.annihilates_iff
      (V := fun d => Source F B I n m d) (DirectionalJetIBP.mixedDerivatives (I := I) n m) d f.toLinearMap

/-- The single input at positive degree is the previously proved coefficient type. -/
def positiveInputEquiv (n m d : ℕ) : Coefficient rhoF rhoB sigma n m (d + 1) ≃ₗ[ℂ]
    CovariantJetIBP.Coefficient (DirectionalJetIBP.mixedDerivatives (I := I) n m)
      (action rhoF rhoB sigma n m) d := LinearEquiv.refl ℂ _

@[simp] theorem positive_map (n m d : ℕ) (f : Coefficient rhoF rhoB sigma n m (d + 1)) :
    coefficientEquiv rhoF rhoB sigma n m (d + 1) f =
      DirectionalJetIBP.mixedCoefficientEquiv sigma rhoF rhoB n m d f := rfl

omit [Fintype I] in
/-- Zero-order jets intertwine even when the symmetry also mixes directions. -/
theorem zeroMap_action (n m : ℕ) (h : H) (p : Original F B n m) :
    MixedJetSource.zeroMap (I := I) n m (originalAction rhoF rhoB n m h p) =
      JetFunctor.sourceAction (JetDirections.combined rhoF sigma) (JetDirections.combined rhoB sigma)
        n m h (MixedJetSource.zeroMap n m p) := by
  have he : (MixedJetSource.zeroMap (I := I) n m).comp (originalAction rhoF rhoB n m h) =
      (JetFunctor.sourceAction (JetDirections.combined rhoF sigma) (JetDirections.combined rhoB sigma)
        n m h).comp (MixedJetSource.zeroMap n m) := by
    apply MixedPowerDescent.ext (A := JetLinear.Field F) (B := JetLinear.Field B) n m
    intro v w
    simp [MixedJetSource.zeroMap, originalAction, JetFunctor.sourceAction, MixedWeightSupport.pure,
      Representation.tprod_apply, TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti,
      SymmetricPower.map_tprod, JetDirections.combined_zero, Function.comp_def]
  exact LinearMap.congr_fun he p

def zeroSourceEquiv (n m : ℕ) : Representation.Equiv (originalAction rhoF rhoB n m)
    (action rhoF rhoB sigma n m 0) :=
  Representation.Equiv.mk (MixedJetSource.zeroEquiv n m) (by
    intro h
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change MixedJetSource.embed n m (MixedJetSource.zeroMap n m (originalAction rhoF rhoB n m h p)) =
      JetFunctor.mixedAction (JetDirections.combined rhoF sigma) (JetDirections.combined rhoB sigma) h
        (MixedJetSource.embed n m (MixedJetSource.zeroMap n m p))
    rw [zeroMap_action, JetFunctor.embed_action])

/-- Import old nonderivative coefficients into the uniform derivative-side input. -/
def nonDerivativeEquiv (n m : ℕ) : InvariantCoefficientTransport.Invariants
    (originalAction rhoF rhoB n m) ≃ₗ[ℂ] Coefficient rhoF rhoB sigma n m 0 :=
  (InvariantCoefficientTransport.alongEquiv (zeroSourceEquiv rhoF rhoB sigma n m)).trans
    (RelationInputExtension.emptyEquiv (JetInputAdapter.values _ _)).symm

omit [Fintype I] in
@[simp] theorem nonDerivative_evaluation (n m : ℕ)
    (f : InvariantCoefficientTransport.Invariants (originalAction rhoF rhoB n m))
    (p : Original F B n m) : (nonDerivativeEquiv rhoF rhoB sigma n m f).val
      (MixedJetSource.zeroEquiv n m p) = f p := by
  change f ((zeroSourceEquiv rhoF rhoB sigma n m).toLinearEquiv.symm
    ((zeroSourceEquiv rhoF rhoB sigma n m).toLinearEquiv p)) = f p
  rw [LinearEquiv.symm_apply_apply]

omit [Fintype I] in
@[simp] theorem nonDerivative_reconstruction (n m : ℕ)
    (f : Coefficient rhoF rhoB sigma n m 0) (p : Original F B n m) :
    (nonDerivativeEquiv rhoF rhoB sigma n m).symm f p = f.val (MixedJetSource.zeroEquiv n m p) := rfl

@[simp] theorem nonDerivative_extraction (n m : ℕ)
    (f : InvariantCoefficientTransport.Invariants (originalAction rhoF rhoB n m))
    (p : Original F B n m) : coefficientEquiv rhoF rhoB sigma n m 0
      (nonDerivativeEquiv rhoF rhoB sigma n m f)
      ((relations n m 0).mkQ (MixedJetSource.zeroEquiv n m p)) = f p := by
  rw [extraction, nonDerivative_evaluation]

end
end Math.MixedOperatorInput
