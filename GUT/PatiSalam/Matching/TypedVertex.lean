import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenResidualCoordinates
import Math.RepresentationTheory.Content.MixedSinglePatternEvaluation

open Physics
open Math Representation ExternalInvariantTensor
open scoped TensorProduct
namespace GUT.PatiSalam.TypedVertex
noncomputable section
def flavor (_ : DeltaLOneSignedInput.Species) := Representation.trivial ℂ Unit ℂ
def scalarFlavor (_ : BnvMixedInput.ScalarSpecies) := Representation.trivial ℂ Unit ℂ
def line := Representation.trivial ℂ Unit ℂ
def pairLine := Representation.TensorProduct.rid ℂ line
def fourLine := (tensorEquiv pairLine pairLine).trans pairLine
def fiveLine := (tensorEquiv fourLine (Representation.Equiv.refl line)).trans pairLine
def flavorCoeff (p : Fin 4) : IntertwiningMap
    (BnvSevenFieldTensor.flavorTensor flavor scalarFlavor
      (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p)) line :=
  fiveLine.toIntertwiningMap

def first : (p : Fin 4) → BnvSevenLocalTransport.Index p :=
  fun p => match p with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0

def raw (p : Fin 4) :=
  (ExternalInvariantTensor.coefficient (BnvSevenLocalTransport.pairing p (first p))
    (flavorCoeff p)).comp
      (BnvSevenFieldTensor.regroup flavor scalarFlavor
        (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p)).toIntertwiningMap
def ordered (p : Fin 4) := BnvSevenFieldTensor.evaluateMap flavor scalarFlavor
  (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p) (raw p)
theorem invariant (p : Fin 4) : MixedSinglePatternAssembly.Invariant
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
    (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p) (ordered p) :=
  ((BnvSevenFieldTensor.tensorDescent flavor scalarFlavor
    (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p)).symm (raw p)).property

def assembled (p : Fin 4) := MixedSinglePatternAssembly.assemble
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
  (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p)
  (ordered p) (invariant p)

theorem assembled_mem (p : Fin 4) : assembled p ∈
    Math.MixedSinglePatternAssembly.familySpace
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
      (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p) := by
  simpa only [assembled] using MixedSinglePatternAssembly.assemble_mem
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
    (BnvSevenPatternDescent.pattern p) (BnvSevenPatternDescent.scalar p)
    (ordered p) (invariant p)

open SMEpsilonTensor StandardSMContragredient

def rrInputs (a b c : Color) (l : Weak) (s t u v : WeylSpinor.Space) :
    ∀ i, DeltaLOneSignedFields.Field (F := fun _ => ℂ)
      (BnvSevenPatternDescent.pattern 0 i) :=
  fun i => match i with
  | 0 => (a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (1:ℂ)
  | 1 => (b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (1:ℂ)
  | 2 => (c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (1:ℂ)
  | 3 => (weakDualLinearEquiv l ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (1:ℂ)
def higgsInput (h : Weak) : BnvMixedInput.ScalarField (S := fun _ => ℂ) 1 :=
  weakDualLinearEquiv h ⊗ₜ[ℂ] (1:ℂ)

theorem rr_ordered (a b c : Color) (l h : Weak) (s t u v : WeylSpinor.Space) :
    ordered 0 (rrInputs a b c l s t u v) (higgsInput h) =
      eps3 a b c * eps2 l h * eps2 s t * eps2 u v := by
  change raw 0 (((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
    ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ]
    (((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
    ((weakDualLinearEquiv l ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (1:ℂ)))) ⊗ₜ[ℂ]
    (higgsInput h)) = _
  change (BnvSevenLocalTransport.pairing 0 0
    ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h)) * flavorCoeff 0 ((((1:ℂ) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
        ((1:ℂ) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ] (1:ℂ)) = _
  have hc : flavorCoeff 0 ((((1:ℂ) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
        ((1:ℂ) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ] (1:ℂ)) = 1 := by
    change (1:ℂ) • (((1:ℂ) • (1:ℂ)) • ((1:ℂ) • (1:ℂ))) = 1
    simp
  rw [hc, mul_one]
  change BnvSevenLocal.pairing 0 (BnvSevenLocalTransport.localEquiv 0
    ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h)) = _
  have he : BnvSevenLocalTransport.localEquiv 0
    ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h) =
    (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (l ⊗ₜ[ℂ] h)) ⊗ₜ[ℂ]
      ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)) := by
    change (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ]
      (weakDualLinearEquiv.symm (weakDualLinearEquiv l) ⊗ₜ[ℂ]
        weakDualLinearEquiv.symm (weakDualLinearEquiv h))) ⊗ₜ[ℂ]
      ((1:ℂ) • ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v))) = _
    rw [one_smul, weakDualLinearEquiv.symm_apply_apply, weakDualLinearEquiv.symm_apply_apply]
  rw [he]
  change (eps3 a b c * eps2 l h) * (eps2 s t * eps2 u v) = _
  ring

def lrInputs (a b c : Color) (x z l : Weak) (s t u v : WeylSpinor.Space) :
    ∀ i, DeltaLOneSignedFields.Field (F := fun _ => ℂ)
      (BnvSevenPatternDescent.pattern 1 i) := fun i => match i with
  | 0 => ((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (1:ℂ)
  | 1 => ((b ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (1:ℂ)
  | 2 => (c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (1:ℂ)
  | 3 => (weakDualLinearEquiv l ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (1:ℂ)

theorem lr_ordered (a b c : Color) (x z l h : Weak) (s t u v : WeylSpinor.Space) :
    ordered 1 (lrInputs a b c x z l s t u v) (higgsInput h) =
      eps3 a b c * eps2 x z * eps2 l h * eps2 s t * eps2 u v := by
  change raw 1 ((((((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
    (((b ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ]
    (((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
    ((weakDualLinearEquiv l ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (1:ℂ)))) ⊗ₜ[ℂ]
    (higgsInput h)) = _
  change (BnvSevenLocalTransport.pairing 1 0
    (((((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h)) * flavorCoeff 1 ((((1:ℂ) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
        ((1:ℂ) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ] (1:ℂ)) = _
  have hc : flavorCoeff 1 ((((1:ℂ) ⊗ₜ[ℂ] (1:ℂ)) ⊗ₜ[ℂ]
        ((1:ℂ) ⊗ₜ[ℂ] (1:ℂ))) ⊗ₜ[ℂ] (1:ℂ)) = 1 := by
    change (1:ℂ) • (((1:ℂ) • (1:ℂ)) • ((1:ℂ) • (1:ℂ))) = 1
    simp
  rw [hc, mul_one]
  change BnvSevenLocal.mixedFourWeakPairing 0 (BnvSevenLocalTransport.localEquiv 1
    (((((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h)) = _
  have he : BnvSevenLocalTransport.localEquiv 1
    (((((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (weakDualLinearEquiv l ⊗ₜ[ℂ] v)))
      ⊗ₜ[ℂ] weakDualLinearEquiv h) =
    (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (l ⊗ₜ[ℂ] h))) ⊗ₜ[ℂ]
      ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] t)) := by
    change (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ]
      ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (weakDualLinearEquiv.symm (weakDualLinearEquiv l) ⊗ₜ[ℂ]
        weakDualLinearEquiv.symm (weakDualLinearEquiv h)))) ⊗ₜ[ℂ]
      (TensorProduct.comm ℂ _ _ ((1:ℂ) • ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)))) = _
    rw [one_smul, weakDualLinearEquiv.symm_apply_apply, weakDualLinearEquiv.symm_apply_apply]
    rfl
  rw [he]
  change (eps3 a b c * (eps2 x z * eps2 l h)) * (eps2 s t * eps2 u v) = _
  ring

def familyCoefficient (p : Fin 4) : BnvSevenPatternDescent.family flavor scalarFlavor p :=
  ⟨assembled p, assembled_mem p⟩

theorem admitted (p : Fin 4) : assembled p ∈ BnvMixedInput.bnvSector flavor scalarFlavor 4 1 :=
  BnvSevenPatternDescent.family_bnv flavor scalarFlavor p (familyCoefficient p)

def rrProbe := rrInputs (colorBasis 0) (colorBasis 1) (colorBasis 2) (weakBasis 1)
  (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
def neutralHiggs := higgsInput (weakBasis 0)
def rrExteriorProbe := MixedWeightSupport.pure
  (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 i) (rrProbe i))
  (fun _ : Fin 1 => Pi.single (BnvSevenPatternDescent.scalar 0) neutralHiggs)

theorem rr_stabilizer : TypedPatternAlternation.stabilizer
    (BnvSevenPatternDescent.pattern 0) = {1, Equiv.swap 1 2} := by decide +kernel

theorem rr_probe_value : assembled 0 rrExteriorProbe = -(1/2:ℂ) := by
  rw [show assembled 0 rrExteriorProbe = _ from
    MixedSinglePatternEvaluation.assembly_value
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
      (BnvSevenPatternDescent.pattern 0) (BnvSevenPatternDescent.scalar 0)
      (ordered 0) (invariant 0) rrProbe neutralHiggs]
  rw [rr_stabilizer]
  simp only [Finset.card_insert_of_notMem (by decide : (1:Equiv.Perm (Fin 4)) ∉ {Equiv.swap (1:Fin 4) 2}),
    Finset.card_singleton, Finset.sum_insert (by decide : (1:Equiv.Perm (Fin 4)) ∉ {Equiv.swap (1:Fin 4) 2}),
    Finset.sum_singleton]
  have hi : (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 ((1:Equiv.Perm (Fin 4)) i)) (rrProbe ((1:Equiv.Perm (Fin 4)) i))
      (BnvSevenPatternDescent.pattern 0 i)) = rrProbe := by
    funext i; simp
  have hs : (fun i => Pi.single (BnvSevenPatternDescent.pattern 0 (Equiv.swap 1 2 i))
      (rrProbe (Equiv.swap 1 2 i)) (BnvSevenPatternDescent.pattern 0 i)) =
    rrInputs (colorBasis 0) (colorBasis 2) (colorBasis 1) (weakBasis 1)
      (weakBasis 0) (weakBasis 0) (weakBasis 1) (weakBasis 1) := by
    funext i; fin_cases i <;> simp [rrProbe, rrInputs, BnvSevenPatternDescent.pattern, Equiv.swap_apply_def]
      <;> exact Pi.single_eq_same _ _
  rw [hi, hs]
  simp only [rrProbe, neutralHiggs, rr_ordered]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply]

theorem rr_nonzero : assembled 0 ≠ 0 := by
  intro hz
  have h := rr_probe_value
  rw [hz] at h
  norm_num at h

def lrProbe := lrInputs (colorBasis 0) (colorBasis 1) (colorBasis 2)
  (weakBasis 0) (weakBasis 1) (weakBasis 1)
  (weakBasis 0) (weakBasis 1) (weakBasis 0) (weakBasis 1)
def lrExteriorProbe := MixedWeightSupport.pure
  (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 i) (lrProbe i))
  (fun _ : Fin 1 => Pi.single (BnvSevenPatternDescent.scalar 1) neutralHiggs)

theorem lr_stabilizer : TypedPatternAlternation.stabilizer
    (BnvSevenPatternDescent.pattern 1) = {1, Equiv.swap 0 1} := by decide +kernel

theorem lr_probe_value : assembled 1 lrExteriorProbe = -(1:ℂ) := by
  rw [show assembled 1 lrExteriorProbe = _ from
    MixedSinglePatternEvaluation.assembly_value
      (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
      (BnvSevenPatternDescent.pattern 1) (BnvSevenPatternDescent.scalar 1)
      (ordered 1) (invariant 1) lrProbe neutralHiggs]
  rw [lr_stabilizer]
  simp only [Finset.card_insert_of_notMem (by decide : (1:Equiv.Perm (Fin 4)) ∉ {Equiv.swap (0:Fin 4) 1}),
    Finset.card_singleton, Finset.sum_insert (by decide : (1:Equiv.Perm (Fin 4)) ∉ {Equiv.swap (0:Fin 4) 1}),
    Finset.sum_singleton]
  have hi : (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 ((1:Equiv.Perm (Fin 4)) i))
      (lrProbe ((1:Equiv.Perm (Fin 4)) i)) (BnvSevenPatternDescent.pattern 1 i)) = lrProbe := by
    funext i; simp
  have hs : (fun i => Pi.single (BnvSevenPatternDescent.pattern 1 (Equiv.swap 0 1 i))
      (lrProbe (Equiv.swap 0 1 i)) (BnvSevenPatternDescent.pattern 1 i)) =
    lrInputs (colorBasis 1) (colorBasis 0) (colorBasis 2)
      (weakBasis 1) (weakBasis 0) (weakBasis 1)
      (weakBasis 1) (weakBasis 0) (weakBasis 0) (weakBasis 1) := by
    funext i; fin_cases i <;> simp [lrProbe, lrInputs, BnvSevenPatternDescent.pattern, Equiv.swap_apply_def]
      <;> exact Pi.single_eq_same _ _
  rw [hi, hs]
  simp only [lrProbe, neutralHiggs, lr_ordered]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply]

theorem lr_nonzero : assembled 1 ≠ 0 := by
  intro hz
  have h := lr_probe_value
  rw [hz] at h
  norm_num at h

end
end GUT.PatiSalam.TypedVertex
