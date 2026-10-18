import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RepresentationTheory.Basic

/-! Faithful finite cyclic characters and their scalar representations. -/
namespace Math.CyclicCharge
set_option autoImplicit false
noncomputable section
variable {N : ℕ} [NeZero N]

abbrev Group (N : ℕ) := Multiplicative (ZMod N)

def representation (q : ZMod N) : Representation ℂ (Group N) ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (ZMod.stdAddChar (q * Multiplicative.toAdd g))
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [mul_add, AddChar.map_add_eq_mul]

@[simp] theorem action (q : ZMod N) (g : Group N) (x : ℂ) :
    representation q g x = ZMod.stdAddChar (q * Multiplicative.toAdd g) * x := rfl

theorem neutral_iff (q : ZMod N) :
    (∀ g : Group N, ZMod.stdAddChar (q * Multiplicative.toAdd g) = 1) ↔ q = 0 := by
  constructor
  · intro h
    have hq := h (Multiplicative.ofAdd (1 : ZMod N))
    have hz : ZMod.stdAddChar q = ZMod.stdAddChar (0 : ZMod N) := by simpa using hq
    exact ZMod.injective_stdAddChar hz
  · rintro rfl g
    simp

theorem sum_action (q r : ZMod N) (g : Group N) :
    representation (q+r) g 1 = representation q g 1 * representation r g 1 := by
  simp [add_mul, AddChar.map_add_eq_mul]

theorem dual_action (q : ZMod N) (g : Group N) (phi : Module.Dual ℂ ℂ) (x : ℂ) :
    (representation q).dual g phi x =
      ZMod.stdAddChar ((-q) * Multiplicative.toAdd g) * phi x := by
  change phi (representation q g⁻¹ x) = _
  change phi (ZMod.stdAddChar (q * Multiplicative.toAdd g⁻¹) • x) = _
  rw [map_smul]
  simp [neg_mul]

end
end Math.CyclicCharge
