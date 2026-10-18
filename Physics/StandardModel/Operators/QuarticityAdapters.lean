import Physics.StandardModel.Operators.ComposableBLSupport
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.CyclicCharge

/-! Actual selected right-neutrino/eta adapters, with fermionic exterior statistics. -/
namespace GUT.QuarticityAdapters
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput SMEpsilonTensor
open scoped TensorProduct
abbrev H := CyclicCharge.Group 4 × CyclicCharge.Group 2
abbrev P := (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × H

@[reducible] local instance : AddCommGroup (⋀[ℂ]^2 WeylSpinor.Space) := inferInstance
@[reducible] local instance : AddCommGroup ((⋀[ℂ]^2 WeylSpinor.Space) ⊗[ℂ] ℂ) := inferInstance

def chi (g : H) : AddChar (ℤ × ℤ) ℂ where
  toFun q := ZMod.stdAddChar ((q.1 : ZMod 4) * Multiplicative.toAdd g.1) *
    ZMod.stdAddChar ((q.2 : ZMod 2) * Multiplicative.toAdd g.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, add_mul, AddChar.map_add_eq_mul]
    ring

theorem chi_mul (g h : H) (q : ℤ × ℤ) : chi (g*h) q = chi g q * chi h q := by
  simp [chi, mul_add, AddChar.map_add_eq_mul]
  ring

theorem compensated (g : H) : chi g (1,1) * chi g (1,1) * chi g (2,0) = 1 := by
  rw [← (chi g).map_add_eq_mul, ← (chi g).map_add_eq_mul]
  change chi g (4,2) = 1
  change ZMod.stdAddChar ((4 : ZMod 4) * _) * ZMod.stdAddChar ((2 : ZMod 2) * _) = 1
  rw [show (4 : ZMod 4) = 0 by decide, show (2 : ZMod 2) = 0 by decide]
  simp

theorem eta_phase_square (g : H) : chi g (2,0) ^ 2 = 1 := by
  rw [pow_two, ← (chi g).map_add_eq_mul]
  change ZMod.stdAddChar ((4 : ZMod 4) * _) * ZMod.stdAddChar ((0 : ZMod 2) * _) = 1
  rw [show (4 : ZMod 4) = 0 by decide]
  simp

theorem eta_phase_real (g : H) : star (chi g (2,0)) = chi g (2,0) := by
  rcases sq_eq_one_iff.mp (eta_phase_square g) with h | h <;> simp [h]

def copies {V : Type*} [AddCommGroup V] [Module ℂ V] (q : ℤ × ℤ) : Representation ℂ H V where
  toFun g := LinearMap.lsmul ℂ V (chi g q)
  map_one' := by ext; simp [chi]
  map_mul' g h := by ext; simp [chi_mul, smul_smul, mul_comm]

/-- Gauge-singlet right-handed neutrino: Z4 charge one and Z2 odd. -/
def neutrino : Representation ℂ P WeylSpinor.Space where
  toFun g := chi g.2 (1,1) • WeylSpinor.right g.1.2
  map_one' := by ext; simp [chi]
  map_mul' g h := by
    ext x
    simp [chi_mul, map_mul, smul_smul, mul_comm]

/-- Complexified coefficient carrier of the real eta singlet. -/
def eta : Representation ℂ P ℂ := (copies (2,0)).comp (MonoidHom.snd _ _)

theorem neutrino_action (g : P) (v : WeylSpinor.Space) :
    neutrino g v = chi g.2 (1,1) • WeylSpinor.right g.1.2 v := rfl

theorem eta_action (g : P) (v : ℂ) : eta g v = chi g.2 (2,0) * v := rfl

theorem neutrino_gauge_neutral (g : StandardSMGaugeTensor.GaugeGroup) (v : WeylSpinor.Space) :
    neutrino ((g,1),1) v = v := by simp [neutrino, chi]

theorem eta_gauge_neutral (g : StandardSMGaugeTensor.GaugeGroup) (v : ℂ) :
    eta ((g,1),1) v = v := by simp [eta, copies, chi]

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
      (chi g.2 (1,1) * chi g.2 (1,1)) * eps2 x y := by
  change eps2 (chi g.2 (1,1) • WeylSpinor.right g.1.2 x)
    (chi g.2 (1,1) • WeylSpinor.right g.1.2 y) = _
  rw [eps2_smul_left, eps2_smul_right]
  have he := IntertwiningMap.isIntertwining _ _ WeylSpinor.epsilonRight g.1.2 (x ⊗ₜ[ℂ] y)
  change eps2 (WeylSpinor.right g.1.2 x) (WeylSpinor.right g.1.2 y) = eps2 x y at he
  rw [he]
  ring

abbrev Bare := IntertwiningMap (neutrino.exteriorPower 2) (Representation.trivial ℂ P ℂ)
abbrev Dressed := IntertwiningMap ((neutrino.exteriorPower 2).tprod eta)
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
      eta g z = epsilonExterior (exteriorPower.ιMulti ℂ 2 v) * z
    rw [Representation.exteriorPower_apply_ιMulti, epsilonExterior_apply, epsilonExterior_apply]
    change eps2 (neutrino g (v 0)) (neutrino g (v 1)) * (chi g.2 (2,0) * z) = _
    rw [epsilon_neutrino]
    calc
      _ = (chi g.2 (1,1) * chi g.2 (1,1) * chi g.2 (2,0)) * (eps2 (v 0) (v 1) * z) := by ring
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
def detector : P := (1,(Multiplicative.ofAdd (1 : ZMod 4),1))

theorem detector_square : chi detector.2 (1,1) * chi detector.2 (1,1) ≠ 1 := by
  rw [← (chi detector.2).map_add_eq_mul]
  change chi detector.2 (2,2) ≠ 1
  change ZMod.stdAddChar ((2 : ZMod 4)*1) * ZMod.stdAddChar ((2 : ZMod 2)*0) ≠ 1
  simp only [mul_one, mul_zero, AddChar.map_zero_eq_one, mul_one]
  intro h
  have he := ZMod.injective_stdAddChar (h.trans (ZMod.stdAddChar (N := 4)).map_zero_eq_one.symm)
  exact (by decide : (2 : ZMod 4) ≠ 0) he

theorem bare_forbidden (f : Bare) : f = 0 := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have he := IntertwiningMap.isIntertwining _ _ f detector (exteriorPower.ιMulti ℂ 2 v)
  rw [Representation.exteriorPower_apply_ιMulti] at he
  have hn : (fun i => neutrino detector (v i)) = fun i => chi detector.2 (1,1) • v i := by
    funext i
    change chi detector.2 (1,1) • WeylSpinor.right 1 (v i) = _
    simp
  change f (exteriorPower.ιMulti ℂ 2 (fun i => neutrino detector (v i))) = f (exteriorPower.ιMulti ℂ 2 v) at he
  rw [hn, (exteriorPower.ιMulti ℂ 2).map_smul_univ, map_smul] at he
  simp only [Fin.prod_univ_two, smul_eq_mul] at he
  have hz : (chi detector.2 (1,1) * chi detector.2 (1,1) - 1) * f (exteriorPower.ιMulti ℂ 2 v) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr detector_square)

def smFlavor (u : Species) : Representation ℂ H ℂ := copies (lepton u,0)
def smScalar (_ : BnvMixedInput.ScalarSpecies) : Representation ℂ H ℂ := copies (0,0)
def blCharacter (g : H) : AddChar (ℤ × ℤ) ℂ where
  toFun q := chi g (q.2,0)
  map_zero_eq_one' := by simp [chi]
  map_add_eq_mul' q r := by
    change chi g ((q.2+r.2),0) = _
    exact (chi g).map_add_eq_mul (q.2,0) (r.2,0)

theorem lTwo_detect (q : ℤ × ℤ) (h : q.2.natAbs = 2) : ∃ g : H, blCharacter g q ≠ 1 := by
  have hz : (q.2 : ZMod 4) ≠ 0 := by
    intro he
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd q.2 4).mp he
    omega
  obtain ⟨g,hg⟩ := (MixedChargeSelection.cyclic_detect_iff (q.2 : ZMod 4)).mpr hz
  refine ⟨(g,1), ?_⟩
  simpa [blCharacter, chi, MixedChargeSelection.cyclicCharacter] using hg

theorem sm_lTwo_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input smFlavor smScalar (fun q => q.2.natAbs = 2) n m, f = 0 := by
  apply ComposableBLSupport.forbidden _ _ _ blCharacter
  · intro g u v; rfl
  · intro g u v; rfl
  · intro n m p s ht; exact lTwo_detect _ ht
end
end GUT.QuarticityAdapters
