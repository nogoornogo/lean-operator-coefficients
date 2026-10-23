import Math.RepresentationTheory.Exterior.TopExteriorCauchy
import Math.RepresentationTheory.Exterior.SymmetricCauchy

/-! A color-volume column followed by the weak/spin row component. -/
namespace Math.ExtremeCauchyBlocks
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G A B C : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] {n : ℕ}

def rowColumn (basis : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (b : Representation ℂ G B) (c : Representation ℂ G C)
    (ha : ∀ g, LinearMap.det (a g) = 1) :
    IntertwiningMap ((b.symmetricPower n).tprod (c.symmetricPower n))
      ((a.tprod (b.tprod c)).exteriorPower n) :=
  (TopExteriorCauchy.intertwiner basis a (b.tprod c) ha).comp
    (SymmetricCauchy.intertwiner b c n)

theorem diagonal (basis : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (b : Representation ℂ G B) (c : Representation ℂ G C)
    (ha : ∀ g, LinearMap.det (a g) = 1) (v : B) (w : C) :
    rowColumn basis a b c ha (SymmetricPower.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin n => w)) =
      exteriorPower.ιMulti ℂ n (fun i => basis i ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) := by
  change TopExteriorCauchy.map basis
    (SymmetricCauchy.map n (SymmetricPower.tprod ℂ (fun _ => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ => w))) = _
  rw [SymmetricCauchy.diagonal, TopExteriorCauchy.diagonal]

theorem nonzero (basis : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (b : Representation ℂ G B) (c : Representation ℂ G C)
    (ha : ∀ g, LinearMap.det (a g) = 1) (v : B) (w : C)
    (φ : Module.Dual ℂ (B ⊗[ℂ] C)) (hv : φ (v ⊗ₜ[ℂ] w) = 1) :
    rowColumn basis a b c ha ≠ 0 := by
  intro he
  have hh := DFunLike.congr_fun he (SymmetricPower.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ]
    SymmetricPower.tprod ℂ (fun _ : Fin n => w))
  change TopExteriorCauchy.map basis
    (SymmetricCauchy.map n (SymmetricPower.tprod ℂ (fun _ => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ => w))) = 0 at hh
  rw [SymmetricCauchy.diagonal] at hh
  exact TopExteriorCauchy.diagonal_nonzero basis (v ⊗ₜ[ℂ] w) φ hv hh

theorem injective (basis : Module.Basis (Fin n) ℂ A)
    (a : Representation ℂ G A) (b : Representation ℂ G B) (c : Representation ℂ G C)
    (ha : ∀ g, LinearMap.det (a g) = 1)
    [IsIrreducible ((b.symmetricPower n).tprod (c.symmetricPower n))]
    (v : B) (w : C) (φ : Module.Dual ℂ (B ⊗[ℂ] C))
    (hv : φ (v ⊗ₜ[ℂ] w) = 1) :
    Function.Injective (rowColumn basis a b c ha) :=
  (IsIrreducible.injective_or_eq_zero (rowColumn basis a b c ha)).resolve_right
    (nonzero basis a b c ha v w φ hv)

end
end Math.ExtremeCauchyBlocks
