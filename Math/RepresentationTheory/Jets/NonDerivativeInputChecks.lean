import Math.RepresentationTheory.Jets.DerivativeInterface
import Math.RepresentationTheory.Jets.JetAdapterControls

/-! Actual old nonderivative coefficients consumed by the unified input.
Off-shell zero-degree compatibility is not an identification after EOM. -/
namespace Math.NonDerivativeInputChecks
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

@[reducible] local instance {F B : Type*} (n m : ℕ) :
    AddCommGroup (MixedJetSource.Original F B n m) := inferInstance
@[reducible] local instance {F B : Type*} (n m : ℕ) :
    Module ℂ (MixedJetSource.Original F B n m) := inferInstance

namespace Bridge
variable {F B I H : Type*} [Group H] [Fintype I]
  (rhoF : Representation ℂ H (JetLinear.Field F))
  (rhoB : Representation ℂ H (JetLinear.Field B))
  (sigma : Representation ℂ H (JetDirections.Direction I)) (n m : ℕ)

abbrev Old := InvariantCoefficientTransport.Invariants (MixedJetSource.originalAction rhoF rhoB n m)
abbrev unified := DerivativeInterface.graded rhoF rhoB sigma n m 0
def toUnified : Old rhoF rhoB n m ≃ₗ[ℂ] (unified rhoF rhoB sigma n m).Coefficient :=
  DerivativeInterface.fromNonDerivative rhoF rhoB sigma n m

theorem no_ibp : (unified rhoF rhoB sigma n m).relations = ⊥ := rfl

theorem old_roundtrip (f : Old rhoF rhoB n m) :
    (toUnified rhoF rhoB sigma n m).symm (toUnified rhoF rhoB sigma n m f) = f :=
  (toUnified rhoF rhoB sigma n m).symm_apply_apply f

theorem unified_roundtrip (f : (unified rhoF rhoB sigma n m).Coefficient) :
    toUnified rhoF rhoB sigma n m ((toUnified rhoF rhoB sigma n m).symm f) = f :=
  (toUnified rhoF rhoB sigma n m).apply_symm_apply f

theorem extraction (f : Old rhoF rhoB n m) (p : MixedJetSource.Original F B n m) :
    (unified rhoF rhoB sigma n m).coefficientEquiv (toUnified rhoF rhoB sigma n m f)
      ((unified rhoF rhoB sigma n m).projection (MixedJetSource.zeroEquiv n m p)) = f p :=
  DerivativeInterface.fromNonDerivative_evaluation rhoF rhoB sigma n m f p

theorem inverse_evaluation (f : (unified rhoF rhoB sigma n m).Coefficient)
    (p : MixedJetSource.Original F B n m) :
    (toUnified rhoF rhoB sigma n m).symm f p = f.val (MixedJetSource.zeroEquiv n m p) := rfl

theorem direction_independence (tau : Representation ℂ H (JetDirections.Direction I))
    (f : Old rhoF rhoB n m) (p : MixedJetSource.Original F B n m) :
    (toUnified rhoF rhoB sigma n m f).val (MixedJetSource.zeroEquiv n m p) =
      (toUnified rhoF rhoB tau n m f).val (MixedJetSource.zeroEquiv n m p) := by
  exact (extraction rhoF rhoB sigma n m f p).trans (extraction rhoF rhoB tau n m f p).symm

theorem nonzero_iff (f : Old rhoF rhoB n m) :
    toUnified rhoF rhoB sigma n m f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro hf hz
    exact hf (by rw [hz,map_zero])
  · intro hf hz
    apply hf
    apply (toUnified rhoF rhoB sigma n m).injective
    rwa [map_zero]

theorem forbidden_iff : (∀ f : Old rhoF rhoB n m, f = 0) ↔
    ∀ f : (unified rhoF rhoB sigma n m).Coefficient, f = 0 := by
  constructor
  · intro h f
    calc
      f = toUnified rhoF rhoB sigma n m ((toUnified rhoF rhoB sigma n m).symm f) :=
        (unified_roundtrip rhoF rhoB sigma n m f).symm
      _ = toUnified rhoF rhoB sigma n m 0 :=
        congrArg (toUnified rhoF rhoB sigma n m) (h _)
      _ = 0 := map_zero _
  · intro h f
    apply (toUnified rhoF rhoB sigma n m).injective
    exact (h _).trans (map_zero _).symm
end Bridge

namespace Statistics
abbrev fermions : Representation ℂ Unit (JetLinear.Field (Fin 2)) := trivial ℂ Unit _
abbrev bosons : Representation ℂ Unit (JetLinear.Field Unit) := trivial ℂ Unit _
abbrev directions : Representation ℂ Unit (JetDirections.Direction (Fin 4)) := trivial ℂ Unit _

def unitInvariant {U : Type*} [AddCommGroup U] [Module ℂ U]
    (r : Representation ℂ Unit U) (f : U →ₗ[ℂ] ℂ) :
    InvariantCoefficientTransport.Invariants r where
  toLinearMap := f
  isIntertwining' g := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    change f.comp (r (1:Unit)) = (trivial ℂ Unit ℂ (1:Unit)).comp f
    rw [map_one,map_one]
    rfl

def bosonProduct (m : ℕ) : SymmetricPowerDescent.symmetricMaps
    (A := JetLinear.Field Unit) (N := ℂ) m :=
  ⟨(MultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ).compLinearMap (fun _ => Finsupp.lapply ()),by
    intro e w
    change (∏ i, w (e i) ()) = ∏ i, w i ()
    exact Equiv.prod_comp e (fun i => w i ())⟩
def evenValue (m : ℕ) := SymmetricPowerDescent.lift m (bosonProduct m)
def oddValue : (⋀[ℂ]^2 (JetLinear.Field (Fin 2))) →ₗ[ℂ] ℂ :=
  exteriorPower.alternatingMapLinearEquiv (Finsupp.basisSingleOne.det)

def oldBose (m : ℕ) : Bridge.Old fermions bosons 0 m :=
  unitInvariant (U := MixedJetSource.Original (Fin 2) Unit 0 m)
    (MixedJetSource.originalAction fermions bosons 0 m)
    ((TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (exteriorPower.zeroEquiv ℂ (JetLinear.Field (Fin 2))).toLinearMap
      (evenValue m)))
def oldMixed (m : ℕ) : Bridge.Old fermions bosons 2 m :=
  unitInvariant (U := MixedJetSource.Original (Fin 2) Unit 2 m)
    (MixedJetSource.originalAction fermions bosons 2 m)
    ((TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map oddValue (evenValue m)))

def bose (m : ℕ) := Bridge.toUnified fermions bosons directions 0 m (oldBose m)
def mixed (m : ℕ) := Bridge.toUnified fermions bosons directions 2 m (oldMixed m)
def boseWord (m : ℕ) : MixedJetSource.Original (Fin 2) Unit 0 m :=
  MixedWeightSupport.pure Fin.elim0 (fun _ => Finsupp.single () 1)
def mixedWord (m : ℕ) (v : Fin 2 → JetLinear.Field (Fin 2)) :
    MixedJetSource.Original (Fin 2) Unit 2 m :=
  MixedWeightSupport.pure v (fun _ => Finsupp.single () 1)

theorem old_bose_value (m : ℕ) : oldBose m (boseWord m) = 1 := by
  simp [oldBose,unitInvariant,boseWord,MixedWeightSupport.pure,evenValue,
    bosonProduct,SymmetricPowerDescent.lift_tprod]

theorem old_mixed_value (m : ℕ) (v : Fin 2 → JetLinear.Field (Fin 2)) :
    oldMixed m (mixedWord m v) = Finsupp.basisSingleOne.det v := by
  simp [oldMixed,unitInvariant,mixedWord,MixedWeightSupport.pure,oddValue,evenValue,
    bosonProduct,SymmetricPowerDescent.lift_tprod,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

theorem bose_value (m : ℕ) :
    (bose m).val (MixedJetSource.zeroEquiv 0 m (boseWord m)) = 1 := by
  exact (Bridge.extraction fermions bosons directions 0 m (oldBose m) (boseWord m)).trans
    (old_bose_value m)

theorem mixed_value (m : ℕ) :
    (mixed m).val (MixedJetSource.zeroEquiv 2 m
      (mixedWord m Finsupp.basisSingleOne)) = 1 := by
  exact (Bridge.extraction fermions bosons directions 2 m (oldMixed m) _).trans
    ((old_mixed_value m _).trans (Module.Basis.det_self _))

theorem swap_value (m : ℕ) :
    (mixed m).val (MixedJetSource.zeroEquiv 2 m
      (mixedWord m ![Finsupp.single 1 1,Finsupp.single 0 1])) = -1 := by
  trans oldMixed m (mixedWord m ![Finsupp.single 1 1,Finsupp.single 0 1])
  · exact Bridge.extraction fermions bosons directions 2 m (oldMixed m) _
  rw [old_mixed_value]
  simp [Module.Basis.det_apply,Module.Basis.toMatrix_apply,Matrix.det_fin_two]

theorem repeated_value (m : ℕ) :
    (mixed m).val (MixedJetSource.zeroEquiv 2 m
      (mixedWord m (fun _ => Finsupp.single 0 1))) = 0 := by
  trans oldMixed m (mixedWord m (fun _ => Finsupp.single 0 1))
  · exact Bridge.extraction fermions bosons directions 2 m (oldMixed m) _
  rw [old_mixed_value]
  simp [Module.Basis.det_apply,Module.Basis.toMatrix_apply,Matrix.det_fin_two]

theorem bose_permutation (m : ℕ) (w : Fin m → JetLinear.Field Unit)
    (e : Equiv.Perm (Fin m)) :
    (bose m).val (MixedJetSource.zeroEquiv 0 m
      (MixedWeightSupport.pure Fin.elim0 (w ∘ e))) =
    (bose m).val (MixedJetSource.zeroEquiv 0 m (MixedWeightSupport.pure Fin.elim0 w)) := by
  have hp : MixedWeightSupport.pure (A := JetLinear.Field (Fin 2)) Fin.elim0 (w ∘ e) =
      MixedWeightSupport.pure Fin.elim0 w := by
    simp only [MixedWeightSupport.pure]
    change _ ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => w (e i)) = _
    rw [SymmetricPower.tprod_equiv]
  exact congrArg (fun p : MixedJetSource.Original (Fin 2) Unit 0 m =>
    (bose m).val (MixedJetSource.zeroEquiv 0 m p)) hp

/-- Explicit pure Bose, pure Fermi, mixed and vacuum inputs are all nonzero. -/
theorem nonzero_examples : bose 4 ≠ 0 ∧ mixed 0 ≠ 0 ∧ mixed 1 ≠ 0 ∧ bose 0 ≠ 0 := by
  have hb (m : ℕ) : bose m ≠ 0 := by
    intro hz
    have hv := bose_value m
    rw [hz] at hv
    exact zero_ne_one hv
  have hm (m : ℕ) : mixed m ≠ 0 := by
    intro hz
    have hv := mixed_value m
    rw [hz] at hv
    exact zero_ne_one hv
  exact ⟨hb 4,hm 0,hm 1,hb 0⟩
end Statistics

namespace FiniteLocal
open JetAdapterControls
abbrev Old := FiniteLocalExtraRelations.Coefficient scalarLocal scalarLocal
  noLocalExchange noLocalExchange Empty.elim
abbrev extended := FiniteLocalExtraRelations.Input scalarLocal scalarLocal
  noLocalExchange noLocalExchange Empty.elim (⊥ : Submodule ℂ (ℂ ⊗[ℂ] ℂ))
def old : Old := ⟨ExternalInvariantTensor.coefficient scalarContraction scalarContraction,
  fun j => nomatch j⟩
def toExtended := (FiniteLocalExtraRelations.emptyEquiv scalarLocal scalarLocal
  noLocalExchange noLocalExchange Empty.elim).symm
def coordinate := FiniteLocalExtraRelations.equiv scalarLocal scalarLocal
  (fun _ : Unit => scalarContraction) (fun _ => (1:ℂ)) scalar_probes scalar_complete
  noLocalExchange noLocalExchange Empty.elim (⊥ : Submodule ℂ (ℂ ⊗[ℂ] ℂ)) (fun _ => bot_le)

theorem old_roundtrip (f : Old) :
    FiniteLocalExtraRelations.emptyEquiv scalarLocal scalarLocal noLocalExchange
      noLocalExchange Empty.elim (toExtended f) = f :=
  (FiniteLocalExtraRelations.emptyEquiv scalarLocal scalarLocal
    noLocalExchange noLocalExchange Empty.elim).apply_symm_apply f

theorem reconstruction (f : extended) : coordinate.symm (coordinate f) = f :=
  coordinate.symm_apply_apply f

theorem evaluation (u w : ℂ) :
    (toExtended old).val.val (u ⊗ₜ[ℂ] w) = u*w := rfl

theorem coordinate_value (u w : ℂ) :
    coordinate (toExtended old)
      ((FiniteLocalExtraRelations.extraRelations scalarLocal scalarLocal
        (fun _ : Unit => scalarContraction) (fun _ => (1:ℂ)) noLocalExchange
        noLocalExchange Empty.elim (⊥ : Submodule ℂ (ℂ ⊗[ℂ] ℂ))).mkQ
          (FiniteLocalExtraRelations.inputMap scalarLocal scalarLocal
            (fun _ : Unit => scalarContraction) (fun _ => (1:ℂ))
            noLocalExchange noLocalExchange Empty.elim (u ⊗ₜ[ℂ] w))) = u*w :=
  FiniteLocalExtraRelations.extraction _ _ _ _ _ _ _ _ _ _ _ _ _
end FiniteLocal

end
end Math.NonDerivativeInputChecks
