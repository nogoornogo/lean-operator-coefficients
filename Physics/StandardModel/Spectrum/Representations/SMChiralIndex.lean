import Physics.StandardModel.Spectrum.Representations.FiniteSMTarget

open Math

/-!
# Dual differences of finite SM weight characters

Duality reverses both weight and residual charge. The oriented SM weights
are disjoint from their negatives regardless of torsion in the label group.
Existing declaration namespaces are retained for compatibility.
-/

set_option autoImplicit false

namespace Physics.StandardWeylDualTarget

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget

variable {A : Type*} [AddCommGroup A]

/-- Contragredient duality, including the residual charge label. -/
def dualCharacter (p : ResolvedCharacter A) : ResolvedCharacter A :=
  Finsupp.mapDomain Neg.neg p

@[simp]
theorem dualCharacter_apply (p : ResolvedCharacter A) (key : ResolvedKey A) :
    dualCharacter p key = p (-key) := by
  simpa [dualCharacter] using Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (Neg.neg : ResolvedKey A → ResolvedKey A)) p (-key)

@[simp]
theorem dualCharacter_dualCharacter (p : ResolvedCharacter A) :
    dualCharacter (dualCharacter p) = p := by
  ext key
  simp

def chiralDifference (p : ResolvedCharacter A) : ResolvedCharacter A :=
  p - dualCharacter p

theorem chiralDifference_apply_selfDual (p : ResolvedCharacter A)
    (key : ResolvedKey A) (hkey : -key = key) : chiralDifference p key = 0 := by
  simp [chiralDifference, hkey]

theorem permuteKey_neg (sigma : Equiv.Perm (Fin 5)) (key : ResolvedKey A) :
    permuteKey sigma (-key) = -permuteKey sigma key := by
  have hraw (w : ReducedWeight) : rawReducedWeight (-w) = -rawReducedWeight w := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · change rawReducedWeight (-w) (Fin.last 4) = -rawReducedWeight w (Fin.last 4)
      rw [rawReducedWeight_last, rawReducedWeight_last, neg_zero]
  apply Prod.ext
  · change normalizeWeight (StandardSU5Orbit.permuteWeight sigma
        (rawReducedWeight (-key.1))) = -permuteReducedWeight sigma key.1
    rw [hraw]
    funext i
    simp [normalizeWeight, permuteReducedWeight, StandardSU5Orbit.permuteWeight,
      sub_eq_add_neg, add_comm]
  · rfl

theorem permuteResolved_dualCharacter
    (sigma : Equiv.Perm (Fin 5)) (p : ResolvedCharacter A) :
    permuteResolved sigma (dualCharacter p) = dualCharacter (permuteResolved sigma p) := by
  unfold permuteResolved dualCharacter
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext key
  exact permuteKey_neg sigma key

theorem chiralDifference_isWeylInvariant
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p) :
    ResolvedWeylInvariant (chiralDifference p) := by
  intro sigma
  change Finsupp.mapDomain (permuteKey sigma) (p - dualCharacter p) = _
  rw [Finsupp.mapDomain_sub]
  change permuteResolved sigma p - permuteResolved sigma (dualCharacter p) = _
  rw [permuteResolved_dualCharacter, hp]
  rfl

/-- Gauge weights alone separate the SM target from its conjugate; no
torsion-free hypothesis on residual charges is involved. -/
theorem smReducedWeight_ne_neg (i j : Fin 15) :
    smReducedWeight i ≠ -smReducedWeight j := by
  revert i j
  decide

end

end Physics.StandardWeylDualTarget
