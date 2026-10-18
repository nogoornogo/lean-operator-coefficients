import Math.LieGroups.Spin.SU5ExteriorAction
import Math.LinearAlgebra.ExteriorEigenbasisTrace
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! An actual basis of the compact half-spin 16, indexed by even subsets.
Eigenvalues are derived from the exterior action, not supplied as a character. -/

set_option autoImplicit false

namespace Math.CompactSpin.HalfSpinEigenbasis

noncomputable section

abbrev Index := {s : Finset (Fin 5) // s.card % 2 = 0}

theorem card_index : Fintype.card Index = 16 := by decide

def vector (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W) (s : Index) :
    HalfSpin.Space 5 :=
  ⟨b.ExteriorAlgebra s.val, by
    rw [TauCeti.mem_spinPlus]
    have h := b.exteriorAlgebra_mem_evenOdd_card s.val
    have hc : (s.val.card : ZMod 2) = 0 := by
      rw [← ZMod.natCast_mod s.val.card 2, s.property, Nat.cast_zero]
    rwa [hc] at h⟩

theorem independent (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W) :
    LinearIndependent ℂ (vector b) := by
  have h := b.ExteriorAlgebra.linearIndependent.comp (fun s : Index => s.val) Subtype.val_injective
  exact LinearIndependent.of_comp (HalfSpin.Space 5).subtype h

def basis (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W) :
    Module.Basis Index ℂ (HalfSpin.Space 5) :=
  basisOfLinearIndependentOfCardEqFinrank' (vector b) (independent b)
    (card_index.trans HalfSpin.finrank_sixteen.symm)

@[simp] theorem basis_apply (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W)
    (s : Index) : basis b s = vector b s := by simp [basis]

theorem eigen (g : SU5) (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W)
    (w : Fin 5 → ℂ) (he : ∀ i, ExteriorComparison.WAction g (b i) = w i • b i)
    (s : Index) :
    HalfSpin.representation 5 (SU5Inclusion g) (basis b s) =
      (∏ i ∈ s.val, w i) • basis b s := by
  apply Subtype.ext
  rw [ExteriorComparison.halfSpin_eq_exterior]
  simp only [basis_apply]
  exact ExteriorEigenbasisTrace.algebra_eigen b (ExteriorComparison.WAction g).toLinearMap w he s.val

theorem character (g : SU5) (b : Module.Basis (Fin 5) ℂ (HalfSpin.polarization 5).W)
    (w : Fin 5 → ℂ) (he : ∀ i, ExteriorComparison.WAction g (b i) = w i • b i) :
    (HalfSpin.representation 5).character (SU5Inclusion g) =
      ∑ s : Index, ∏ i ∈ s.val, w i := by
  classical
  let : LinearOrder Index := linearOrderOfSTO WellOrderingRel
  exact ExteriorEigenbasisTrace.trace_eq_sum (basis b) _ _ (eigen g b w he)

end

end Math.CompactSpin.HalfSpinEigenbasis
