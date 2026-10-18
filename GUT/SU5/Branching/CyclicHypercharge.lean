import Math.RepresentationTheory.Characters.AbelianCharacterPolynomial
import GUT.SU5.Branching.FortyHyperchargeExclusion

namespace GUT.SU5.CyclicHypercharge
set_option autoImplicit false
noncomputable section
open Math
abbrev Group := Multiplicative (ZMod 31)
abbrev Polynomial := ZMod 31 →₀ ℤ
def circle : Group →* Circle := (ZMod.toCircle : AddChar (ZMod 31) Circle).toMonoidHom
def character (k : ZMod 31) : Group →* ℂ where
  toFun g := ZMod.stdAddChar (k * g.toAdd)
  map_one' := by simp
  map_mul' g h := by
    change ZMod.stdAddChar (k * (g.toAdd+h.toAdd)) = _
    rw [mul_add, AddChar.map_add_eq_mul]

theorem character_injective : Function.Injective character := by
  intro k l h
  apply ZMod.injective_stdAddChar
  have he := congrArg (fun f : Group →* ℂ => f (Multiplicative.ofAdd (1 : ZMod 31))) h
  simpa [character] using he

def encode (p : Polynomial) : AbelianActualSpectrum.Polynomial Group := Finsupp.mapDomain character p
def eval (p : Polynomial) (g : Group) : ℂ := AbelianActualSpectrum.eval (encode p) g

theorem eval_injective (p q : Polynomial) (h : ∀ g, eval p g = eval q g) : p=q := by
  have he := AbelianActualSpectrum.eval_injective (encode p) (encode q) h
  exact Finsupp.mapDomain_injective character_injective he

@[simp] theorem eval_single (k : ZMod 31) (n : ℤ) (g : Group) :
    eval (Finsupp.single k n) g = (n : ℂ) * character k g := by
  simp [eval, encode]
@[simp] theorem eval_add (p q : Polynomial) (g : Group) : eval (p+q) g=eval p g+eval q g := by
  simp [eval, encode, Finsupp.mapDomain_add]
@[simp] theorem eval_sub (p q : Polynomial) (g : Group) : eval (p-q) g=eval p g-eval q g := by
  simp [eval, encode, Finsupp.mapDomain_sub]
@[simp] theorem eval_zero (g : Group) : eval 0 g=0 := by simp [eval, encode]
theorem eval_zsmul (n : ℤ) (p : Polynomial) (g : Group) : eval (n • p) g = (n : ℂ) * eval p g := by
  classical
  unfold eval encode AbelianActualSpectrum.eval
  rw [Finsupp.mapDomain_smul, Finsupp.sum_smul_index]
  · simp [Int.cast_mul, Finsupp.mul_sum, mul_assoc]
  · simp
@[simp] theorem eval_sum {I : Type*} (s : Finset I) (p : I → Polynomial) (g : Group) :
    eval (∑ i ∈ s, p i) g = ∑ i ∈ s, eval (p i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem character_integer (k : ℤ) (g : Group) :
    character (k : ZMod 31) g = ((circle g ^ k : Circle) : ℂ) := by
  have h := (ZMod.toCircle : AddChar (ZMod 31) Circle).map_zsmul_eq_zpow k g.toAdd
  change ((ZMod.toCircle ((k : ZMod 31) * g.toAdd) : Circle) : ℂ) = _
  simpa only [zsmul_eq_mul, circle, AddChar.toMonoidHom_apply] using congrArg (fun z : Circle => (z : ℂ)) h

def dual (p : Polynomial) : Polynomial := Finsupp.mapDomain (fun k : ZMod 31 => -k) p
@[simp] theorem dual_apply (p : Polynomial) (k : ZMod 31) : dual p k = p (-k) := by
  simpa [dual] using Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (fun k : ZMod 31 => -k)) p (-k)
theorem eval_dual (p : Polynomial) (g : Group) : eval (dual p) g = eval p g⁻¹ := by
  have hc : character ∘ (fun k : ZMod 31 => -k) =
      AbelianActualSpectrum.dualCharacter ∘ character := by
    funext k
    apply MonoidHom.ext
    intro z
    change ZMod.stdAddChar (-k * z.toAdd) = ZMod.stdAddChar (k * (-z.toAdd))
    congr 1
    ring
  have he : encode (dual p) = AbelianActualSpectrum.dual (encode p) := by
    unfold encode dual AbelianActualSpectrum.dual
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hc]
  change AbelianActualSpectrum.eval (encode (dual p)) g = _
  rw [he, AbelianActualSpectrum.eval_dual]
  rfl

end
end GUT.SU5.CyclicHypercharge
