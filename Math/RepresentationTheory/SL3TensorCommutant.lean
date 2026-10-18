import Math.RepresentationTheory.SL3CompactComparison
import TauCeti.RepresentationTheory.Symmetric.TensorAction.GeneralLinear
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The SL3 tensor-power commutant is the actual permutation-algebra image.
Only the scalar normalization of a general-linear matrix is needed. -/
namespace Math.SL3TensorCommutant
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL3CompactComparison
open scoped TensorProduct

@[reducible] local instance (n : ℕ) : AddCommGroup (⨂[ℂ]^n Vector) := inferInstance

theorem scalar_normalization (g : Matrix.GeneralLinearGroup (Fin 3) ℂ) :
    ∃ (z : ℂ) (s : Group), z ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) ℂ) = z • s.val := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (g : Matrix (Fin 3) (Fin 3) ℂ).det (by decide : 0 < 3)
  have hz0 : z ≠ 0 := by
    intro he
    have hd := Matrix.GeneralLinearGroup.det_ne_zero g
    apply hd
    simpa [he] using hz.symm
  let s : Group := ⟨z⁻¹ • (g : Matrix (Fin 3) (Fin 3) ℂ),by
    rw [Matrix.det_smul,Fintype.card_fin,inv_pow,hz]
    exact inv_mul_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero g)⟩
  refine ⟨z,s,hz0,?_⟩
  change _ = z • (z⁻¹ • _)
  rw [smul_smul,mul_inv_cancel₀ hz0,one_smul]

theorem power_smul (n : ℕ) (z : ℂ) (r : Module.End ℂ Vector) :
    PiTensorProduct.map (fun _ : Fin n => z • r) =
      z^n • PiTensorProduct.map (fun _ : Fin n => r) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,PiTensorProduct.map_tprod,
    LinearMap.smul_apply]
  have he := (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => Vector)).map_smul_univ
    (fun _ => z) (fun i => r (v i))
  simpa using he

theorem generalLinear_action (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 3) ℂ)
    (z : ℂ) (s : Group)
    (he : (g : Matrix (Fin 3) (Fin 3) ℂ) = z • s.val) :
    TauCeti.tensorPowerRep ℂ 3 n g = z^n • (standard.tensorPower n) s := by
  have hbase : TauCeti.stdRep ℂ 3 g = z • standard s := by
    apply LinearMap.ext
    intro v
    change _ = z • (s.val.mulVec v)
    rw [TauCeti.stdRep_apply_apply,he,Matrix.smul_mulVec]
  rw [Representation.tensorPower_apply,Representation.tensorPower_apply,hbase,power_smul]

theorem commutes_generalLinear (n : ℕ) (f : Module.End ℂ (⨂[ℂ]^n Vector))
    (hf : ∀ s, Commute f ((standard.tensorPower n) s)) :
    ∀ g : Matrix.GeneralLinearGroup (Fin 3) ℂ, Commute f (TauCeti.tensorPowerRep ℂ 3 n g) := by
  intro g
  obtain ⟨z,s,_,he⟩ := scalar_normalization g
  rw [generalLinear_action n g z s he]
  exact (hf s).smul_right (z^n)

/-- The conclusion is an actual linear combination of tensor permutations. -/
theorem permutation_image (n : ℕ) (f : Module.End ℂ (⨂[ℂ]^n Vector))
    (hf : ∀ s, Commute f ((standard.tensorPower n) s)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
      TauCeti.permTensorActionAlgHom ℂ 3 n a = f := by
  let : NeZero (n.factorial : ℂ) := ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)⟩
  exact (TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep f).mpr
    (commutes_generalLinear n f hf)

end
end Math.SL3TensorCommutant
