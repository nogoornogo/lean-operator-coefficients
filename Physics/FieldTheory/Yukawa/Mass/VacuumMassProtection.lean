import Physics.FieldTheory.Yukawa.Mass.WeylYukawaMass
import Physics.FieldTheory.Mass.Algebra.InvariantMassProtection

/-! Radical protection for actual UV Yukawa families at a residual-invariant vacuum. -/
set_option autoImplicit false
namespace Physics.VacuumMassProtection
noncomputable section
open Representation InvariantWeylMass WeylYukawaMass InvariantMassProtection

variable {G K S V W P : Type*} [Group G] [Group K]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rhoS : Representation ℂ G S} {rho : Representation ℂ G V}
  {sigma : Representation ℂ G W}
  (bare : SymmetricMass (rho.prod sigma))
  (Y : P → EquivariantYukawa rhoS (rho.prod sigma))
  (f : K →* G) (v : S) (hv : ∀ k, rhoS (f k) v = v)

def mass (p : P) : SymmetricMass (Representation.prod (rho.comp f) (sigma.comp f)) :=
  atVacuumOn bare (Y p) f v hv

theorem cross_apply (p : P) (x : V) (w : W) :
    cross (mass bare Y f v hv p) x w =
      bare.form (x, 0) (0, w) + (Y p).toLinearMap v (x, 0) (0, w) := rfl

variable (B : SymmetricMass (rho.comp f))

theorem extends_iff (p : P) : Extends B (mass bare Y f v hv p) ↔
    ∀ x y, bare.form (x, 0) (y, 0) +
      (Y p).toLinearMap v (x, 0) (y, 0) = B.form x y := Iff.rfl

theorem preserves_iff (p : P) (he : Extends B (mass bare Y f v hv p)) :
    Preserves B (mass bare Y f v hv p) ↔
      ∀ x : B.radical.toSubmodule, ∀ w : W,
        bare.form (x.val, 0) (0, w) +
          (Y p).toLinearMap v (x.val, 0) (0, w) = 0 := by
  rw [InvariantMassProtection.preserves_iff B _ he]
  constructor
  · intro h x w
    exact LinearMap.congr_fun (congrArg (fun C => C x) h) w
  · intro h
    ext x w
    exact h x w

theorem family_iff (he : ∀ p, Extends B (mass bare Y f v hv p)) :
    (∀ p, Preserves B (mass bare Y f v hv p)) ↔
      ∀ p, ∀ x : B.radical.toSubmodule, ∀ w : W,
        bare.form (x.val, 0) (0, w) +
          (Y p).toLinearMap v (x.val, 0) (0, w) = 0 := by
  constructor
  · intro h p
    exact (preserves_iff bare Y f v hv B p (he p)).mp (h p)
  · intro h p
    exact (preserves_iff bare Y f v hv B p (he p)).mpr (h p)

theorem same_evaluation (p q : P)
    (h : (Y p).toLinearMap v = (Y q).toLinearMap v) :
    mass bare Y f v hv p = mass bare Y f v hv q := by
  unfold mass atVacuumOn
  simp only [h]
  rfl

end
end Physics.VacuumMassProtection
