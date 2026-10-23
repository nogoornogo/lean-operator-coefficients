import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Mass.Spectrum.UnitaryVirtualRealization

/-!
# A symmetric bilinear mass on an invariant line

For a fixed invariant vector v, x maps to inner(v,x) complex-linearly.
The product inner(v,x) * inner(v,y), unlike the Hermitian form itself,
is complex-bilinear and symmetric. A nonzero v gives a rank-one mass.
-/

set_option autoImplicit false

namespace Physics.InvariantLineMass

noncomputable section

open UnitaryVirtualRealization InvariantWeylMass

variable {G : Type*} [Group G] (R : ActualUnitaryGroupRepresentation G)

def form (v : R.V) : LinearMap.BilinForm ℂ R.V :=
  (LinearMap.mul ℂ ℂ).compl₁₂ (innerₛₗ ℂ v) (innerₛₗ ℂ v)

@[simp] theorem form_apply (v x y : R.V) :
    form R v x y = inner ℂ v x * inner ℂ v y := rfl

def mass (v : R.V) (hv : ∀ g, R.rho g v = v) : SymmetricMass R.rho where
  form := form R v
  symmetric := ⟨fun x y => mul_comm _ _⟩
  invariant := by
    intro g x y
    have hi (z : R.V) : inner ℂ v (R.rho g z) = inner ℂ v z := by
      simpa only [hv g] using R.unitary g v z
    simp [hi]

theorem form_ne_zero (v : R.V) (hv : v ≠ 0) : form R v ≠ 0 := by
  intro he
  have hz := LinearMap.congr_fun (LinearMap.congr_fun he v) v
  change inner ℂ v v * inner ℂ v v = 0 at hz
  have hi : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv
  exact (mul_ne_zero hi hi) hz

theorem radical_eq_ker (v : R.V) (hv : v ≠ 0) (hi : ∀ g, R.rho g v = v) :
    (mass R v hi).radical.toSubmodule = LinearMap.ker (innerₛₗ ℂ v) := by
  ext x
  rw [SymmetricMass.mem_radical, LinearMap.mem_ker]
  change (∀ y, inner ℂ v x * inner ℂ v y = 0) ↔ inner ℂ v x = 0
  constructor
  · intro h
    exact (mul_eq_zero.mp (h v)).resolve_right (inner_self_ne_zero.mpr hv)
  · intro h y
    rw [h, zero_mul]

theorem radical_finrank_add_one (v : R.V) (hv : v ≠ 0)
    (hi : ∀ g, R.rho g v = v) :
    Module.finrank ℂ (mass R v hi).radical.toSubmodule + 1 = Module.finrank ℂ R.V := by
  rw [radical_eq_ker R v hv hi]
  have hs : Function.Surjective (innerₛₗ ℂ v) := by
    intro z
    refine ⟨(z / inner ℂ v v) • v, ?_⟩
    change inner ℂ v ((z / inner ℂ v v) • v) = z
    rw [inner_smul_right, div_mul_cancel₀ _ (inner_self_ne_zero.mpr hv)]
  have hr : LinearMap.range (innerₛₗ ℂ v) = ⊤ := LinearMap.range_eq_top.mpr hs
  have hd := (innerₛₗ ℂ v).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self] at hd
  omega

end

end Physics.InvariantLineMass
