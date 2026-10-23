import Math.RepresentationTheory.Tensors.InvariantPairing

/-!
# Transport of invariant coefficients through matched quotients

If four actual representations surject equivariantly onto V, V*, W, W*,
their tensor product has a nonzero invariant coefficient. No assumption is
made that the four spaces consist entirely of these matched components.
The existence of the quotient maps is an explicit input, not derived here.
-/

set_option autoImplicit false

namespace Math.InvariantPairing

noncomputable section

open scoped TensorProduct

variable {k H V W A B C D : Type*} [Field k] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
  {rho : Representation k H V} {sigma : Representation k H W}
  {tauA : Representation k H A} {tauB : Representation k H B}
  {tauC : Representation k H C} {tauD : Representation k H D}
  (pA : Representation.IntertwiningMap tauA rho)
  (pB : Representation.IntertwiningMap tauB rho.dual)
  (pC : Representation.IntertwiningMap tauC sigma)
  (pD : Representation.IntertwiningMap tauD sigma.dual)

def pulledCoefficient : Representation.IntertwiningMap
    ((tauA.tprod tauB).tprod (tauC.tprod tauD)) (Representation.trivial k H k) :=
  (pairedCoefficient rho sigma).comp ((pA.tensor pB).tensor (pC.tensor pD))

@[simp] theorem pulledCoefficient_apply (a : A) (b : B) (c : C) (d : D) :
    pulledCoefficient pA pB pC pD ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)) =
      (pB b) (pA a) * (pD d) (pC c) := rfl

theorem exists_pulledCoefficient_eq_one [Nontrivial V] [Nontrivial W]
    (hA : Function.Surjective pA) (hB : Function.Surjective pB)
    (hC : Function.Surjective pC) (hD : Function.Surjective pD) :
    ∃ (a : A) (b : B) (c : C) (d : D),
      pulledCoefficient pA pB pC pD ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)) = 1 := by
  obtain ⟨x, f, y, l, h⟩ := exists_pairedCoefficient_eq_one rho sigma
  obtain ⟨a, rfl⟩ := hA x
  obtain ⟨b, rfl⟩ := hB f
  obtain ⟨c, rfl⟩ := hC y
  obtain ⟨d, rfl⟩ := hD l
  exact ⟨a, b, c, d, h⟩

theorem pulledCoefficient_ne_zero [Nontrivial V] [Nontrivial W]
    (hA : Function.Surjective pA) (hB : Function.Surjective pB)
    (hC : Function.Surjective pC) (hD : Function.Surjective pD) :
    pulledCoefficient pA pB pC pD ≠ 0 := by
  obtain ⟨a, b, c, d, h⟩ := exists_pulledCoefficient_eq_one pA pB pC pD hA hB hC hD
  intro hz
  rw [hz] at h
  exact zero_ne_one h

/-- Equivariance alone does not preserve nonzeroness under pullback. -/
theorem pulledCoefficient_zero_first :
    pulledCoefficient (0 : Representation.IntertwiningMap tauA rho) pB pC pD = 0 := by
  ext a b c d
  simp

end

end Math.InvariantPairing
