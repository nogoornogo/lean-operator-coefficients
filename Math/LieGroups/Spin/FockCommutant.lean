import Math.LieGroups.Spin.PolarizedSpan

/-! The commutant of the real compact Clifford generators is scalar on the
full Fock module. This concerns all generators, not just even Spin elements. -/

set_option autoImplicit false

namespace Math.CompactSpin.Fock

noncomputable section

open Polarized

theorem generator_eq (n : ℕ) (v : RealSpace n) :
    generator n v = (HalfSpin.polarization n).cliffordOperator (coordinates n v) := by
  change TauCeti.spinAction (complexForm n) (HalfSpin.polarization n)
    (cliffordMap n (CliffordAlgebra.ι (realForm n) v)) = _
  rw [cliffordMap_ι, TauCeti.spinAction_ι]

theorem commutes_complex (n : ℕ) (T : Module.End ℂ (Space n))
    (h : ∀ v, Commute T (generator n v)) (v : TauCeti.SplitEvenSpace ℂ n) :
    Commute T ((HalfSpin.polarization n).cliffordOperator v) := by
  let a : TauCeti.SplitEvenSpace ℂ n →ₗ[ℂ] Module.End ℂ (Space n) :=
    (LinearMap.mul ℂ _ T).comp (HalfSpin.polarization n).cliffordOperator
  let b : TauCeti.SplitEvenSpace ℂ n →ₗ[ℂ] Module.End ℂ (Space n) :=
    ((LinearMap.mul ℂ _).flip T).comp (HalfSpin.polarization n).cliffordOperator
  have hab : a = b := PolarizedSpan.linearMap_ext n a b (by
    intro w
    simpa only [a, b, LinearMap.comp_apply, LinearMap.mul_apply', LinearMap.flip_apply,
      ← generator_eq] using (h w).eq)
  exact LinearMap.congr_fun hab v

theorem commutes_all (n : ℕ) (T : Module.End ℂ (Space n))
    (h : ∀ v, Commute T (generator n v)) (A : Module.End ℂ (Space n)) : Commute T A := by
  obtain ⟨x, rfl⟩ := TauCeti.spinAction_surjective (HalfSpin.polarization n) A
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact (Algebra.commutes r T).symm
  | ι v => rw [TauCeti.spinAction_ι]; exact commutes_complex n T h v
  | mul x y hx hy => rw [map_mul]; exact hx.mul_right hy
  | add x y hx hy => rw [map_add]; exact hx.add_right hy

def vacuumScalar (n : ℕ) (T : Module.End ℂ (Space n)) : ℂ :=
  ExteriorAlgebra.algebraMapInv (T 1)

theorem commutant_scalar (n : ℕ) (T : Module.End ℂ (Space n))
    (h : ∀ v, Commute T (generator n v)) : T = vacuumScalar n T • 1 := by
  apply LinearMap.ext
  intro s
  let A : Module.End ℂ (Space n) := ExteriorAlgebra.algebraMapInv.toLinearMap.smulRight s
  have hh := LinearMap.congr_fun (commutes_all n T h A).eq 1
  simpa only [A, vacuumScalar, Module.End.mul_apply, LinearMap.smulRight_apply,
    AlgHom.toLinearMap_apply, map_one, one_smul, LinearMap.smul_apply,
    Module.End.one_apply] using hh

end

end Math.CompactSpin.Fock
