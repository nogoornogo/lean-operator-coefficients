import Math.RepresentationTheory.SixSlotSpeciesRestriction
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Restriction and reconstruction for degree `(2,4)` exterior coefficients. -/
namespace Math.SixSlotRestrictionLift

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section

open Representation SixSlotAlternation SixSlotSpeciesDegree SixSlotSpeciesRestriction
open scoped TensorProduct

section Curry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def evalEmpty : MultilinearMap ℂ (fun _ : Fin 0 => V) ℂ →ₗ[ℂ] ℂ where
  toFun f := f Fin.elim0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def curryOne : MultilinearMap ℂ (fun _ : Fin 1 => V) ℂ →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ evalEmpty).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 1 => V) ℂ).toLinearMap

private def curryTwo : MultilinearMap ℂ (fun _ : Fin 2 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryOne).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 2 => V) ℂ).toLinearMap

private def curryThree : MultilinearMap ℂ (fun _ : Fin 3 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryTwo).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 3 => V) ℂ).toLinearMap

private def curryFour : MultilinearMap ℂ (fun _ : Fin 4 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryThree).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 4 => V) ℂ).toLinearMap

private def curryFive : MultilinearMap ℂ (fun _ : Fin 5 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryFour).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 5 => V) ℂ).toLinearMap

private def currySix : MultilinearMap ℂ (fun _ : Fin 6 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryFive).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 6 => V) ℂ).toLinearMap

end Curry

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

private def inA : A →ₗ[ℂ] Fields A B := LinearMap.inl ℂ A B
private def inB : B →ₗ[ℂ] Fields A B := LinearMap.inr ℂ A B

variable (a : Representation ℂ H A) (b : Representation ℂ H B)

private def precomposeHead
    {V X P Q : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommMonoid P] [Module ℂ P] [AddCommMonoid Q] [Module ℂ Q]
    (i : X →ₗ[ℂ] V) (tail : P →ₗ[ℂ] Q) :
    (V →ₗ[ℂ] P) →ₗ[ℂ] X →ₗ[ℂ] Q :=
  (LinearMap.lcomp ℂ Q i).comp (LinearMap.llcomp ℂ V P Q tail)

private def restrictTailSix :
    (Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ]
      Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ]
      A →ₗ[ℂ] B →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
  let t₆ : (Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
    LinearMap.lcomp ℂ ℂ (inB (A := A) (B := B))
  let t₅ : (Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ]
      B →ₗ[ℂ] B →ₗ[ℂ] ℂ := precomposeHead (inB (A := A) (B := B)) t₆
  let t₄ : (Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ]
      B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ := precomposeHead (inB (A := A) (B := B)) t₅
  let t₃ : (Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ]
      Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
    precomposeHead (inA (A := A) (B := B)) t₄
  let t₂ : (Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ]
      Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] ℂ) →ₗ[ℂ]
      B →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
    precomposeHead (inB (A := A) (B := B)) t₃
  precomposeHead
    (V := Fields A B) (X := A)
    (P := Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ]
      Fields A B →ₗ[ℂ] Fields A B →ₗ[ℂ] ℂ)
    (Q := B →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (inA (A := A) (B := B)) t₂

private def restrictedCurry (f : coefficients a b) :
    A →ₗ[ℂ] B →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
  restrictTailSix (currySix (evaluation a b f).toMultilinearMap)

private def firstPair (f : coefficients a b) :
    (A ⊗[ℂ] B) →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
  TensorProduct.lift (restrictedCurry a b f)

private def secondPair (f : coefficients a b) :
    (A ⊗[ℂ] B) →ₗ[ℂ] (A ⊗[ℂ] B) →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (firstPair a b f p)
  map_add' p q := by ext x y z w; simp [firstPair]
  map_smul' c p := by ext x y z w; simp [firstPair]

private def firstTwoPairs (f : coefficients a b) :
    ((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) →ₗ[ℂ] B →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
  TensorProduct.lift (secondPair a b f)

private def lastPair (f : coefficients a b) :
    ((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) →ₗ[ℂ] (B ⊗[ℂ] B) →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (firstTwoPairs a b f p)
  map_add' p q := by ext x y; simp [firstTwoPairs]
  map_smul' c p := by ext x y; simp [firstTwoPairs]

def linearRestriction (f : coefficients a b) : OrderedSpace A B →ₗ[ℂ] ℂ :=
  TensorProduct.lift (lastPair a b f)

@[simp] theorem linearRestriction_apply (f : coefficients a b)
    (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B) :
    linearRestriction a b f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
      (d₃ ⊗ₜ[ℂ] d₄))) =
      f (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄)) := by
  simp [linearRestriction, lastPair, firstTwoPairs, secondPair, firstPair,
    restrictedCurry, restrictTailSix, precomposeHead, currySix, curryFive,
    curryFour, curryThree, curryTwo, curryOne, evalEmpty, evaluation, slots]
  congr 2

def restriction (f : coefficients a b) : IntertwiningMap (orderedRepresentation a b)
    (Representation.trivial ℂ H ℂ) where
  toLinearMap := linearRestriction a b f
  isIntertwining' h := by
    ext u₁ d₁ u₂ d₂ d₃ d₄
    change f (exteriorPower.ιMulti ℂ 6
      (slots (a h u₁) (a h u₂) (b h d₁) (b h d₂) (b h d₃) (b h d₄))) =
      f (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄))
    have hi := IntertwiningMap.isIntertwining _ _ f h
      (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄))
    rw [Representation.exteriorPower_apply_ιMulti] at hi
    have hv : (fun i => action a b h (slots u₁ u₂ d₁ d₂ d₃ d₄ i)) =
        slots (a h u₁) (a h u₂) (b h d₁) (b h d₂) (b h d₃) (b h d₄) := by
      funext i
      fin_cases i <;> simp [slots, action]
    change f (exteriorPower.ιMulti ℂ 6
      (fun i => action a b h (slots u₁ u₂ d₁ d₂ d₃ d₄ i))) = _ at hi
    rw [hv] at hi
    exact hi

private def patternProject (v : Fin 6 → Fields A B) : Fin 6 → Fields A B :=
  ![((v 0).1, 0), (0, (v 1).2), ((v 2).1, 0), (0, (v 3).2),
    (0, (v 4).2), (0, (v 5).2)]

omit [Module ℂ A] [Module ℂ B] in
private theorem patternProject_perm (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B)
    (p : Equiv.Perm (Fin 6)) (hp : PreservesPattern p) :
    patternProject (slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ p) =
      slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ p := by
  rcases hp with ⟨h0, h2⟩
  rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
  · have : (0 : Fin 6) = 2 := p.injective (h0.trans h2.symm)
    omega
  · funext i
    have hnot (j : Fin 6) (hj0 : j ≠ 0) (hj2 : j ≠ 2) : p j ≠ 0 ∧ p j ≠ 2 := by
      constructor
      · rw [← h0]; exact p.injective.ne hj0
      · rw [← h2]; exact p.injective.ne hj2
    fin_cases i
    · simp [patternProject, slots, h0]
    · generalize hk : p 1 = k; fin_cases k <;> simp_all [patternProject, slots]
    · simp [patternProject, slots, h2]
    · generalize hk : p 3 = k; fin_cases k <;> simp_all [patternProject, slots]
    · generalize hk : p 4 = k; fin_cases k <;> simp_all [patternProject, slots]
    · generalize hk : p 5 = k; fin_cases k <;> simp_all [patternProject, slots]
  · funext i
    have hnot (j : Fin 6) (hj0 : j ≠ 0) (hj2 : j ≠ 2) : p j ≠ 0 ∧ p j ≠ 2 := by
      constructor
      · rw [← h2]; exact p.injective.ne hj2
      · rw [← h0]; exact p.injective.ne hj0
    fin_cases i
    · simp [patternProject, slots, h0]
    · generalize hk : p 1 = k; fin_cases k <;> simp_all [patternProject, slots]
    · simp [patternProject, slots, h2]
    · generalize hk : p 3 = k; fin_cases k <;> simp_all [patternProject, slots]
    · generalize hk : p 4 = k; fin_cases k <;> simp_all [patternProject, slots]
    · generalize hk : p 5 = k; fin_cases k <;> simp_all [patternProject, slots]
  · have : (0 : Fin 6) = 2 := p.injective (h0.trans h2.symm)
    omega

private theorem ordered_restriction (f : coefficients a b) (v : Fin 6 → Fields A B) :
    ordered (linearRestriction a b f) v = evaluation a b f (patternProject v) := by
  simp [ordered, linearRestriction, lastPair, firstTwoPairs, secondPair, firstPair,
    restrictedCurry, restrictTailSix, precomposeHead, currySix, curryFive,
    curryFour, curryThree, curryTwo, curryOne, evalEmpty, patternProject]
  congr 1

theorem restriction_preserves (f : coefficients a b)
    (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B) (p : Equiv.Perm (Fin 6))
    (hp : PreservesPattern p) :
    ordered (linearRestriction a b f)
        (slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ p) =
      Equiv.Perm.sign p •
        linearRestriction a b f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
          (d₃ ⊗ₜ[ℂ] d₄))) := by
  rw [ordered_restriction, patternProject_perm u₁ u₂ d₁ d₂ d₃ d₄ p hp]
  exact (evaluation a b f).map_perm _ p

theorem alternating_restriction_slots (f : coefficients a b)
    (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B) :
    alternating (linearRestriction a b f) (slots u₁ u₂ d₁ d₂ d₃ d₄) =
      48 • f (exteriorPower.ιMulti ℂ 6
        (slots u₁ u₂ d₁ d₂ d₃ d₄)) := by
  rw [alternating_slots_of_preserves (linearRestriction a b f) u₁ u₂ d₁ d₂ d₃ d₄
    (restriction_preserves a b f u₁ u₂ d₁ d₂ d₃ d₄)]
  rw [linearRestriction_apply]

theorem reconstruct (f : coefficients a b) (hf : HasDegree a b f) :
    coefficient a b ((1 / 48 : ℂ) • restriction a b f) = f := by
  apply slots_ext a b _ f (coefficient_hasDegree a b _) hf
  intro u₁ u₂ d₁ d₂ d₃ d₄
  rw [coefficient_apply_ιMulti]
  change alternating ((1 / 48 : ℂ) • linearRestriction a b f)
    (slots u₁ u₂ d₁ d₂ d₃ d₄) = _
  rw [alternating_smul]
  change (1 / 48 : ℂ) *
    alternating (linearRestriction a b f) (slots u₁ u₂ d₁ d₂ d₃ d₄) = _
  rw [alternating_restriction_slots]
  ring

theorem exists_ordered (f : coefficients a b) (hf : HasDegree a b f) :
    ∃ g : IntertwiningMap (orderedRepresentation a b) (Representation.trivial ℂ H ℂ),
      coefficient a b g = f :=
  ⟨(1 / 48 : ℂ) • restriction a b f, reconstruct a b f hf⟩

end
end Math.SixSlotRestrictionLift
