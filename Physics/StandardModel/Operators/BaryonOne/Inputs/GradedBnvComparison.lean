import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenCompleteness
import Math.RepresentationTheory.Coefficients.GradedMixedCompleteness

open Math

/-! Actual signed SM/Higgs inputs for the degree-uniform residual quotient theorem. -/
namespace Physics.GradedBnvComparison
set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section
open Representation DeltaLOneSignedInput
open scoped TensorProduct
variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))

def scalarLocal (u : BnvMixedInput.ScalarSpecies) :=
  (BnvMixedInput.scalarGauge u).comp
    (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group)
def fermion := TypedMixedSeparatedHom.fieldF DeltaLOneSignedFields.localField flavor
def boson := TypedMixedSeparatedHom.fieldB scalarLocal scalarFlavor

theorem fermion_eq : fermion flavor = DeltaLOneSignedFields.field flavor := by
  funext u
  ext ⟨g,h⟩ : 1
  apply TensorProduct.ext'
  intro x y
  simp [fermion, TypedMixedSeparatedHom.fieldF, TypedMixedLocalHom.fermion,
    CommutingActionHom.action_apply, TypedMixedSeparatedHom.localF,
    TypedMixedSeparatedHom.residualF, DeltaLOneSignedFields.field,
    ExternalInvariantTensor.external, Representation.tprod_apply]

theorem boson_eq : boson scalarFlavor = BnvMixedInput.scalarField scalarFlavor := by
  funext u
  ext ⟨g,h⟩ : 1
  apply TensorProduct.ext'
  intro x y
  simp [boson, TypedMixedSeparatedHom.fieldB, TypedMixedLocalHom.boson,
    CommutingActionHom.action_apply, TypedMixedSeparatedHom.localB,
    TypedMixedSeparatedHom.residualB, BnvMixedInput.scalarField, scalarLocal,
    ExternalInvariantTensor.external, Representation.tprod_apply]

def allowed {n m : ℕ} (labels : Fin n → Species) (_scalars : Fin m → BnvMixedInput.ScalarSpecies) :=
  (∑ i, baryon (labels i)) ≠ 0

theorem stable {n m : ℕ} (v : Fin n → Species) (w : Fin m → BnvMixedInput.ScalarSpecies)
    (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)) :
    allowed (v ∘ p) (w ∘ q) ↔ allowed v w := by
  have he : (∑ i, baryon (v (p i))) = ∑ i, baryon (v i) :=
    Fintype.sum_equiv p _ _ (by intro i; rfl)
  simp only [allowed, Function.comp_apply, he]

theorem supportPresentation (n m : ℕ) : BnvMixedInput.bnvSector flavor scalarFlavor n m =
    MixedSpeciesProjection.supportSpace (allowed (n := n) (m := m))
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor) := by
  apply Submodule.ext
  intro f
  constructor
  · intro hf labels scalars hn v w
    exact hf labels scalars v w (not_ne_iff.mp hn)
  · intro hf labels scalars v w hz
    exact hf labels scalars (by change ¬ ((∑ i, baryon (labels i)) ≠ 0); simp [hz]) v w

private def supportCongr {P Q J : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] [Group J]
    {V : P → Type*} {W : Q → Type*}
    [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
    [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
    {n m : ℕ} (allow : (Fin n → P) → (Fin m → Q) → Prop)
    (r r' : ∀ u, Representation ℂ J (V u))
    (t t' : ∀ u, Representation ℂ J (W u)) (hr : r = r') (ht : t = t') :
    MixedSpeciesProjection.supportSpace allow r t ≃ₗ[ℂ]
      MixedSpeciesProjection.supportSpace allow r' t' := by
  subst r'; subst t'
  exact LinearEquiv.refl ℂ _

private def ofSupportEq {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (U V : Submodule ℂ A) (h : U = V)
    (e : V ≃ₗ[ℂ] B) : U ≃ₗ[ℂ] B := (LinearEquiv.ofEq U V h).trans e

def supportEquiv (n m : ℕ) := by
  let e₂ : MixedSpeciesProjection.supportSpace (allowed (n := n) (m := m))
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor) ≃ₗ[ℂ]
      MixedSpeciesProjection.supportSpace (allowed (n := n) (m := m))
        (fermion flavor) (boson scalarFlavor) :=
    supportCongr (V := DeltaLOneSignedFields.Field (F := F))
      (W := BnvMixedInput.ScalarField (S := S)) (allowed (n := n) (m := m))
      _ _ _ _ (fermion_eq flavor).symm (boson_eq scalarFlavor).symm
  exact ofSupportEq (BnvMixedInput.bnvSector flavor scalarFlavor n m)
    (MixedSpeciesProjection.supportSpace (allowed (n := n) (m := m))
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor))
    (supportPresentation flavor scalarFlavor n m) e₂

def perDegreeEquiv (n m : ℕ) := by
  classical
  let e₁ := supportEquiv flavor scalarFlavor n m
  let e₂ := GradedMixedCompleteness.selectedEquiv DeltaLOneSignedFields.localField
      scalarLocal flavor scalarFlavor n m allowed stable
  exact e₁.trans e₂

abbrev Residual (n m : ℕ) := ∀ x : MixedContentOrbits.Selected (allowed (n := n) (m := m)),
  GradedMixedCompleteness.Factor DeltaLOneSignedFields.localField scalarLocal
    flavor scalarFlavor n m x.val

def sixComparison : Residual flavor scalarFlavor 4 0 ≃ₗ[ℂ]
    BnvSixResidualCompleteness.ResidualProduct flavor :=
  (perDegreeEquiv flavor scalarFlavor 4 0).symm.trans
    ((BnvZeroBosonBridge.equiv flavor scalarFlavor).trans
      (BnvSixResidualCompleteness.equiv flavor))

def sevenComparison : Residual flavor scalarFlavor 4 1 ≃ₗ[ℂ]
    (∀ i : Fin 8, BnvSevenSignedCoordinates.Factor flavor scalarFlavor i) :=
  (perDegreeEquiv flavor scalarFlavor 4 1).symm.trans
    (BnvSevenSignedCoordinates.equiv flavor scalarFlavor)

abbrev ResidualProduct := Residual flavor scalarFlavor 4 0 × Residual flavor scalarFlavor 4 1

def boundedSevenEquiv : BnvMixedInput.bounded flavor scalarFlavor 7 ≃ₗ[ℂ]
    ResidualProduct flavor scalarFlavor :=
  (BnvSevenDegreeDecomposition.equiv flavor scalarFlavor).trans
    (LinearEquiv.prodCongr (perDegreeEquiv flavor scalarFlavor 4 0)
      (perDegreeEquiv flavor scalarFlavor 4 1))

def comparison : ResidualProduct flavor scalarFlavor ≃ₗ[ℂ]
    BnvSevenCompleteness.ResidualProduct flavor scalarFlavor :=
  (boundedSevenEquiv flavor scalarFlavor).symm.trans
    (BnvSevenCompleteness.equiv flavor scalarFlavor)

attribute [local irreducible] supportEquiv perDegreeEquiv boundedSevenEquiv comparison

private theorem inverseDiagram {A B C : Type*} [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] [AddCommMonoid C] [Module ℂ C]
    (e : A ≃ₗ[ℂ] B) (k : A ≃ₗ[ℂ] C) :
    (e.symm : B → A) = (k.symm : C → A) ∘ (e.symm.trans k : B → C) := by
  funext q
  exact (k.symm_apply_apply (e.symm q)).symm

theorem extraction_commutes (f : BnvMixedInput.bounded flavor scalarFlavor 7) :
    comparison flavor scalarFlavor (boundedSevenEquiv flavor scalarFlavor f) =
      BnvSevenCompleteness.extract flavor scalarFlavor f := by
  unfold comparison
  exact congrArg (BnvSevenCompleteness.equiv flavor scalarFlavor)
    ((boundedSevenEquiv flavor scalarFlavor).symm_apply_apply f)

theorem reconstruction_commutes (q : ResidualProduct flavor scalarFlavor) :
    (boundedSevenEquiv flavor scalarFlavor).symm q =
      BnvSevenCompleteness.reconstruct flavor scalarFlavor (comparison flavor scalarFlavor q) := by
  unfold comparison
  exact congrFun (inverseDiagram (boundedSevenEquiv flavor scalarFlavor)
    (BnvSevenCompleteness.equiv flavor scalarFlavor)) q

theorem reconstruct_extract (f : BnvMixedInput.bounded flavor scalarFlavor 7) :
    (boundedSevenEquiv flavor scalarFlavor).symm (boundedSevenEquiv flavor scalarFlavor f) = f :=
  (boundedSevenEquiv flavor scalarFlavor).symm_apply_apply f

theorem extract_reconstruct (q : ResidualProduct flavor scalarFlavor) :
    boundedSevenEquiv flavor scalarFlavor ((boundedSevenEquiv flavor scalarFlavor).symm q) = q :=
  (boundedSevenEquiv flavor scalarFlavor).apply_symm_apply q

theorem forbidden_iff : (∀ f : BnvMixedInput.bounded flavor scalarFlavor 7, f = 0) ↔
    ∀ q : ResidualProduct flavor scalarFlavor, q = 0 := by
  constructor
  · intro h q
    exact (boundedSevenEquiv flavor scalarFlavor).symm.injective
      ((h _).trans (boundedSevenEquiv flavor scalarFlavor).symm.map_zero.symm)
  · intro h f
    exact (boundedSevenEquiv flavor scalarFlavor).injective
      ((h _).trans (boundedSevenEquiv flavor scalarFlavor).map_zero.symm)

theorem nonzero_iff : (∃ f : BnvMixedInput.bounded flavor scalarFlavor 7, f ≠ 0) ↔
    ∃ q : ResidualProduct flavor scalarFlavor, q ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (forbidden_iff flavor scalarFlavor)

end
end Physics.GradedBnvComparison
