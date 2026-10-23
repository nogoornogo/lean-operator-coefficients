import Physics.StandardModel.Operators.Selection.QuarticityAdapters
import Math.LinearAlgebra.Selection.MixedSelectionRequests

/-! Selected Ma et al. Z3 singlet sectors; scalar chi2 is complex. -/
namespace Physics.MaZ3Mixed
set_option autoImplicit false
noncomputable section
open Math Representation SMEpsilonTensor
open scoped TensorProduct
abbrev H := CyclicCharge.Group 3
abbrev P := (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H
@[reducible] local instance : AddCommGroup (⋀[ℂ]^2 WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 WeylSpinor.Space) ⊗[ℂ] ℂ) := inferInstance

def phase (g : H) : ℂ := MixedChargeSelection.cyclicCharacter g (1 : ZMod 3)

theorem compensated (g : H) : phase g * phase g * phase g = 1 := by
  unfold phase
  rw [← (MixedChargeSelection.cyclicCharacter g).map_add_eq_mul,
    ← (MixedChargeSelection.cyclicCharacter g).map_add_eq_mul]
  change MixedChargeSelection.cyclicCharacter g (0 : ZMod 3) = 1
  exact (MixedChargeSelection.cyclicCharacter g).map_zero_eq_one

def neutrino : Representation ℂ P WeylSpinor.Space where
  toFun g := phase g.2 • WeylSpinor.right g.1.2
  map_one' := by ext; simp [phase, MixedChargeSelection.cyclicCharacter]
  map_mul' g h := by
    ext x
    simp [phase, MixedChargeSelection.cyclicCharacter, mul_add,
      AddChar.map_add_eq_mul, map_mul, smul_smul, mul_comm]

/-- Selected complex chi2 field: printed residual phase equals the lepton phase. -/
def scalar : Representation ℂ P ℂ :=
  (CyclicCharge.representation (1 : ZMod 3)).comp (MonoidHom.snd _ _)

theorem scalar_action (g : P) (v : ℂ) : scalar g v = phase g.2 * v := rfl

def epsilonExterior : (⋀[ℂ]^2 WeylSpinor.Space) →ₗ[ℂ] ℂ :=
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating :
    WeylSpinor.Space [⋀^Fin 2]→ₗ[ℂ] ℂ)

theorem epsilonExterior_apply (v : Fin 2 → WeylSpinor.Space) :
    epsilonExterior (exteriorPower.ιMulti ℂ 2 v) = eps2 (v 0) (v 1) := by
  rw [epsilonExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det (Matrix.of v) = _
  rw [Matrix.det_fin_two]
  rfl

theorem epsilon_neutrino (g : P) (x y : WeylSpinor.Space) :
    eps2 (neutrino g x) (neutrino g y) =
      (phase g.2 * phase g.2) * eps2 x y := by
  change eps2 (phase g.2 • WeylSpinor.right g.1.2 x)
    (phase g.2 • WeylSpinor.right g.1.2 y) = _
  rw [eps2_smul_left, eps2_smul_right]
  have he := IntertwiningMap.isIntertwining _ _ WeylSpinor.epsilonRight g.1.2 (x ⊗ₜ[ℂ] y)
  change eps2 (WeylSpinor.right g.1.2 x) (WeylSpinor.right g.1.2 y) = eps2 x y at he
  rw [he]
  ring

abbrev Bare := IntertwiningMap (neutrino.exteriorPower 2) (Representation.trivial ℂ P ℂ)
abbrev Dressed := IntertwiningMap ((neutrino.exteriorPower 2).tprod scalar)
  (Representation.trivial ℂ P ℂ)

def dressed : Dressed where
  toLinearMap := TensorProduct.lift ((LinearMap.mul ℂ ℂ).comp epsilonExterior)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro z
    change epsilonExterior ((neutrino.exteriorPower 2) g (exteriorPower.ιMulti ℂ 2 v)) *
      scalar g z = epsilonExterior (exteriorPower.ιMulti ℂ 2 v) * z
    rw [Representation.exteriorPower_apply_ιMulti, epsilonExterior_apply, epsilonExterior_apply]
    change eps2 (neutrino g (v 0)) (neutrino g (v 1)) * (phase g.2 * z) = _
    rw [epsilon_neutrino]
    calc
      _ = (phase g.2 * phase g.2 * phase g.2) * (eps2 (v 0) (v 1) * z) := by ring
      _ = _ := by rw [compensated, one_mul]

theorem dressed_evaluation : dressed
    (exteriorPower.ιMulti ℂ 2 ![weakBasis 0,weakBasis 1] ⊗ₜ[ℂ] (1 : ℂ)) = 1 := by
  change epsilonExterior (exteriorPower.ιMulti ℂ 2 ![weakBasis 0,weakBasis 1]) * 1 = 1
  rw [epsilonExterior_apply]
  simp

theorem dressed_nonzero : dressed ≠ 0 := by
  intro h
  have he := dressed_evaluation
  rw [h] at he
  exact zero_ne_one he

theorem exists_dressed : ∃ f : Dressed, f ≠ 0 := ⟨dressed,dressed_nonzero⟩

/-- A residual element detecting the bare Majorana pair. -/
def detector : P := (1,Multiplicative.ofAdd (1 : ZMod 3))

theorem detector_square : phase detector.2 * phase detector.2 ≠ 1 := by
  unfold phase
  rw [← (MixedChargeSelection.cyclicCharacter detector.2).map_add_eq_mul]
  change ZMod.stdAddChar ((2 : ZMod 3) * 1) ≠ 1
  simp only [mul_one]
  intro h
  have he := ZMod.injective_stdAddChar
    (h.trans (ZMod.stdAddChar (N := 3)).map_zero_eq_one.symm)
  exact (by decide : (2 : ZMod 3) ≠ 0) he

theorem bare_forbidden (f : Bare) : f = 0 := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have he := IntertwiningMap.isIntertwining _ _ f detector (exteriorPower.ιMulti ℂ 2 v)
  rw [Representation.exteriorPower_apply_ιMulti] at he
  have hn : (fun i => neutrino detector (v i)) = fun i => phase detector.2 • v i := by
    funext i
    change phase detector.2 • WeylSpinor.right 1 (v i) = _
    simp
  change f (exteriorPower.ιMulti ℂ 2 (fun i => neutrino detector (v i))) = f (exteriorPower.ιMulti ℂ 2 v) at he
  rw [hn, (exteriorPower.ιMulti ℂ 2).map_smul_univ, map_smul] at he
  simp only [Fin.prod_univ_two, smul_eq_mul] at he
  have hz : (phase detector.2 * phase detector.2 - 1) * f (exteriorPower.ιMulti ℂ 2 v) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr detector_square)

open MixedSelectionRequests SelectionCriteria
inductive Target where | bare | dressed deriving DecidableEq

def domain : Target → Type
  | .bare => Bare
  | .dressed => Dressed
instance (t : Target) : Zero (domain t) := by cases t <;> unfold domain <;> infer_instance

def request : Request Target := ⟨{t | t = .bare}, {t | t = .dressed}⟩

theorem satisfies : Satisfies domain request := by
  constructor
  · intro t ht; change t = .bare at ht; subst t; exact bare_forbidden
  · intro t ht; change t = .dressed at ht; subst t; exact exists_dressed
end
end Physics.MaZ3Mixed
