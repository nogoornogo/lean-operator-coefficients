import Physics.FieldTheory.Spinor.SixWeylInvariant
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! A multilinear interface to the six-right-Weyl invariant classification. -/
namespace GUT.SixWeylMultilinear

set_option autoImplicit false
noncomputable section
open SMEpsilonTensor

abbrev Spin := WeylSpinor.Space
abbrev Coefficient := MultilinearMap ℂ (fun _ : Fin 6 => Spin) ℂ
def IsInvariant (f : Coefficient) : Prop :=
  ∀ g v, f (fun i => WeylSpinor.right g (v i)) = f v

def curried (f : Coefficient) : SixWeylInvariant.Coefficient :=
  f.curryRight.curryRight.curryRight.curryRight.curryRight.curryRight Fin.elim0

@[simp] theorem curried_apply (f : Coefficient) (a b c d e x : Spin) :
    curried f a b c d e x = f ![a,b,c,d,e,x] := by
  simp only [curried, MultilinearMap.curryRight_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

def pairingValue (p : Fin 5) (v : Fin 6 → Spin) : ℂ :=
  SixWeylInvariant.pairingValue p (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)

def pairing (p : Fin 5) : Coefficient :=
  MultilinearMap.mk' (pairingValue p)
    (by intro v i x y; fin_cases p <;> fin_cases i <;>
      simp [pairingValue, SixWeylInvariant.pairingValue, Function.update,
        eps2, Fin.ext_iff] <;> ring)
    (by intro v i z x; fin_cases p <;> fin_cases i <;>
      simp [pairingValue, SixWeylInvariant.pairingValue, Function.update,
        eps2, Fin.ext_iff, smul_eq_mul] <;> ring)

@[simp] theorem pairing_apply (p : Fin 5) (v : Fin 6 → Spin) :
    pairing p v = pairingValue p v := rfl

theorem pairing_invariant (p : Fin 5) : IsInvariant (pairing p) := by
  intro g v
  have he (s t : Spin) : SMEpsilonTensor.eps2 (WeylSpinor.right g s)
      (WeylSpinor.right g t) = SMEpsilonTensor.eps2 s t := by
    rw [WeylSpinor.right_apply, WeylSpinor.right_apply]
    exact SMEpsilonTensor.eps2_invariant _ (WeylSpinor.conjugate g).property s t
  fin_cases p <;> simp only [pairing_apply, pairingValue,
    SixWeylInvariant.pairingValue, he]

theorem basis_ext {f g : Coefficient}
    (h : ∀ idx : Fin 6 → Fin 2,
      f (fun i => weakBasis (idx i)) = g (fun i => weakBasis (idx i))) : f = g := by
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin 2))
  simpa only [weakBasis, Pi.basisFun_apply] using h

theorem exists_pairing_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃ c : Fin 5 → ℂ, f = ∑ p, c p • pairing p := by
  have hi : SixWeylInvariant.IsInvariant (curried f) := by
    intro g a b c d e x
    have hv : (fun i => WeylSpinor.right g (![a,b,c,d,e,x] i)) =
        ![WeylSpinor.right g a, WeylSpinor.right g b, WeylSpinor.right g c,
          WeylSpinor.right g d, WeylSpinor.right g e, WeylSpinor.right g x] := by
      ext i; fin_cases i <;> rfl
    simpa only [curried_apply, hv] using hf g ![a,b,c,d,e,x]
  obtain ⟨c, hc⟩ := SixWeylInvariant.exists_pairing_coordinates (curried f) hi
  refine ⟨c, basis_ext ?_⟩
  intro idx
  have hv : ![weakBasis (idx 0), weakBasis (idx 1), weakBasis (idx 2),
      weakBasis (idx 3), weakBasis (idx 4), weakBasis (idx 5)] =
      (fun i => weakBasis (idx i)) := by ext i; fin_cases i <;> rfl
  simpa [SixWeylInvariant.basisValue, hv, pairingValue] using
    hc (idx 0) (idx 1) (idx 2) (idx 3) (idx 4) (idx 5)

def basisValue (f : Coefficient) (idx : Fin 6 → Fin 2) : ℂ :=
  f (fun i => weakBasis (idx i))

/-- The triangular inverse of the five noncrossing pairing probes. -/
def coordinates (f : Coefficient) : Fin 5 → ℂ := ![
  basisValue f ![0,1,0,1,0,1] + basisValue f ![0,1,0,0,1,1] +
    basisValue f ![0,0,1,1,0,1] + basisValue f ![0,0,1,0,1,1] +
    2 * basisValue f ![0,0,0,1,1,1],
  basisValue f ![0,1,0,0,1,1] + basisValue f ![0,0,1,0,1,1] +
    basisValue f ![0,0,0,1,1,1],
  basisValue f ![0,0,1,1,0,1] + basisValue f ![0,0,1,0,1,1] +
    basisValue f ![0,0,0,1,1,1],
  basisValue f ![0,0,1,0,1,1] + basisValue f ![0,0,0,1,1,1],
  basisValue f ![0,0,0,1,1,1]]

def reconstruct (c : Fin 5 → ℂ) : Coefficient := ∑ p, c p • pairing p

theorem coordinates_reconstruct (c : Fin 5 → ℂ) :
    coordinates (reconstruct c) = c := by
  ext p
  fin_cases p <;>
    simp [coordinates, reconstruct, basisValue, Fin.sum_univ_succ,
      pairingValue, SixWeylInvariant.pairingValue, eps2, weakBasis]
  all_goals ring

theorem reconstruct_coordinates (f : Coefficient) (hf : IsInvariant f) :
    reconstruct (coordinates f) = f := by
  obtain ⟨c, hc⟩ := exists_pairing_coordinates f hf
  change f = reconstruct c at hc
  rw [hc, coordinates_reconstruct]

theorem eq_of_coordinates {f g : Coefficient} (hf : IsInvariant f)
    (hg : IsInvariant g) (h : coordinates f = coordinates g) : f = g := by
  rw [← reconstruct_coordinates f hf, ← reconstruct_coordinates g hg, h]

theorem existsUnique_pairing_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃! c : Fin 5 → ℂ, reconstruct c = f := by
  refine ⟨coordinates f, reconstruct_coordinates f hf, ?_⟩
  intro c hc
  rw [← hc, coordinates_reconstruct]

end
end GUT.SixWeylMultilinear
