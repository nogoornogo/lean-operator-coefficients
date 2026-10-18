import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# The integer lattice of continuous circle homomorphisms

Every continuous group homomorphism from the circle to itself is a unique
integer power map.  The proof lifts the homomorphism through
`Circle.exp : Real -> Circle`.  Uniqueness of covering-space lifts makes the
lift additive; continuity then makes it real-linear, and periodicity forces
its slope to be an integer.

The coordinatewise consequence classifies continuous homomorphisms from the
circle to the two-torus by pairs of integers.
-/

namespace Math
namespace CircleHomLattice

open Function

noncomputable section

/-- The continuous circle endomorphism with integer exponent `n`. -/
def circlePowerHom (n : ℤ) : Circle →ₜ* Circle where
  toMonoidHom := zpowGroupHom n
  continuous_toFun := continuous_zpow n

@[simp]
theorem circlePowerHom_apply (n : ℤ) (z : Circle) :
    circlePowerHom n z = z ^ n :=
  rfl

/-- Every continuous circle endomorphism is a unique integer power map. -/
theorem existsUnique_eq_circlePowerHom (f : Circle →ₜ* Circle) :
    ∃! n : ℤ, f = circlePowerHom n := by
  let fexp : C(ℝ, Circle) :=
    ⟨fun x => f (Circle.exp x),
      f.continuous.comp Circle.exp.continuous⟩
  obtain ⟨F, hF, hF_unique⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      fexp (0 : ℝ) (0 : ℝ) (by simp [fexp])
  have hF_lifts (x : ℝ) : Circle.exp (F x) = f (Circle.exp x) := by
    simpa [fexp, Function.comp_def] using congrFun hF.2 x
  have hF_add (x y : ℝ) : F (x + y) = F x + F y := by
    let G : C(ℝ, ℝ) :=
      ⟨fun t => F (x + t) - F x,
        (F.continuous.comp (continuous_const.add continuous_id)).sub
          continuous_const⟩
    have hG : G 0 = 0 ∧ Circle.exp ∘ G = fexp := by
      constructor
      · simp [G]
      · funext t
        change Circle.exp (F (x + t) - F x) = f (Circle.exp t)
        rw [Circle.exp_sub, hF_lifts, hF_lifts, Circle.exp_add,
          map_mul]
        simp
    have hGF : G = F := hF_unique G hG
    have hAtY := congrArg (fun H : C(ℝ, ℝ) => H y) hGF
    change F (x + y) - F x = F y at hAtY
    linarith
  let Fadd : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := hF.1
      map_add' := hF_add }
  have hF_linear (x : ℝ) : F x = x * F 1 := by
    simpa [Fadd, smul_eq_mul] using
      (map_real_smul Fadd F.continuous x (1 : ℝ))
  have hF_period : Circle.exp (F (2 * Real.pi)) = 1 := by
    rw [hF_lifts]
    simp
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hF_period
  have hF_one : F 1 = (n : ℝ) := by
    rw [hF_linear] at hn
    have hTwoPi : 0 < 2 * Real.pi := by positivity
    nlinarith
  refine ⟨n, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro z
    change f z = z ^ n
    calc
      f z = f (Circle.exp (Complex.arg z)) := by rw [Circle.exp_arg]
      _ = Circle.exp (F (Complex.arg z)) := (hF_lifts _).symm
      _ = Circle.exp ((n : ℝ) * Complex.arg z) := by
        rw [hF_linear, hF_one]
        rw [mul_comm]
      _ = Circle.exp (Complex.arg z) ^ n :=
        Circle.exp_intCast_mul _ _
      _ = z ^ n := by rw [Circle.exp_arg]
  · intro m hm
    let Fm : C(ℝ, ℝ) :=
      ⟨fun x => (m : ℝ) * x, continuous_const.mul continuous_id⟩
    have hFm : Fm 0 = 0 ∧ Circle.exp ∘ Fm = fexp := by
      constructor
      · simp [Fm]
      · funext x
        change Circle.exp ((m : ℝ) * x) = f (Circle.exp x)
        rw [hm]
        exact Circle.exp_intCast_mul x m
    have hFmF : Fm = F := hF_unique Fm hFm
    have hAtOne := congrArg (fun H : C(ℝ, ℝ) => H 1) hFmF
    change (m : ℝ) * 1 = F 1 at hAtOne
    have hmn : (m : ℝ) = (n : ℝ) := by
      simpa [hF_one] using hAtOne
    exact_mod_cast hmn

/-- Integer exponents give an injective parameterization of continuous circle
endomorphisms. -/
theorem circlePowerHom_injective : Function.Injective circlePowerHom := by
  intro m n h
  exact ((existsUnique_eq_circlePowerHom (circlePowerHom m)).unique
    (y₁ := n) (y₂ := m) h rfl).symm

/-- The continuous homomorphism into the two-torus with exponent pair
`(m, n)`. -/
def circlePairPowerHom (mn : ℤ × ℤ) : Circle →ₜ* Circle × Circle :=
  (circlePowerHom mn.1).prod (circlePowerHom mn.2)

@[simp]
theorem circlePairPowerHom_apply (mn : ℤ × ℤ) (z : Circle) :
    circlePairPowerHom mn z = (z ^ mn.1, z ^ mn.2) :=
  rfl

/-- Continuous homomorphisms from the circle to the two-torus are classified
by a unique pair of integer exponents. -/
theorem existsUnique_eq_circlePairPowerHom
    (f : Circle →ₜ* Circle × Circle) :
    ∃! mn : ℤ × ℤ, f = circlePairPowerHom mn := by
  let fColor : Circle →ₜ* Circle :=
    (ContinuousMonoidHom.fst Circle Circle).comp f
  let fWeak : Circle →ₜ* Circle :=
    (ContinuousMonoidHom.snd Circle Circle).comp f
  obtain ⟨m, hm, hm_unique⟩ := existsUnique_eq_circlePowerHom fColor
  obtain ⟨n, hn, hn_unique⟩ := existsUnique_eq_circlePowerHom fWeak
  refine ⟨(m, n), ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro z
    apply Prod.ext
    · simpa [fColor] using congrArg (fun g : Circle →ₜ* Circle => g z) hm
    · simpa [fWeak] using congrArg (fun g : Circle →ₜ* Circle => g z) hn
  · intro mn hmn
    apply Prod.ext
    · apply hm_unique mn.1
      apply ContinuousMonoidHom.ext
      intro z
      have hAtZ := congrArg (fun g : Circle →ₜ* Circle × Circle => (g z).1) hmn
      simpa [fColor] using hAtZ
    · apply hn_unique mn.2
      apply ContinuousMonoidHom.ext
      intro z
      have hAtZ := congrArg (fun g : Circle →ₜ* Circle × Circle => (g z).2) hmn
      simpa [fWeak] using hAtZ

/-- The integer lattice as an explicit equivalence of underlying types. -/
def integerPairEquivCircleTorusHom :
    (ℤ × ℤ) ≃ (Circle →ₜ* Circle × Circle) :=
  Equiv.ofBijective circlePairPowerHom
    ⟨fun mn pq h => ((existsUnique_eq_circlePairPowerHom
        (circlePairPowerHom mn)).unique
          (y₁ := pq) (y₂ := mn) h rfl).symm,
      fun f => by
        obtain ⟨mn, hmn⟩ := (existsUnique_eq_circlePairPowerHom f).exists
        exact ⟨mn, hmn.symm⟩⟩

/-!
## Faithful circles and primitive exponent pairs
-/

/-- The only common `d`-th root of unity is `1` exactly when `d = 1`.
The converse direction uses the explicit point `exp (2*pi/d)` for `d >= 2`.
-/
theorem forall_pow_eq_one_imp_eq_one_iff (d : ℕ) :
    (∀ z : Circle, z ^ d = 1 → z = 1) ↔ d = 1 := by
  constructor
  · intro h
    by_cases hd0 : d = 0
    · subst d
      have hNeg : (-1 : Circle) = 1 := h (-1) (by simp)
      have hCoe := congrArg (fun z : Circle => (z : ℂ)) hNeg
      norm_num at hCoe
    · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
      by_contra hd1
      have hdTwo : 2 ≤ d := by omega
      let theta : ℝ := 2 * Real.pi / d
      let z : Circle := Circle.exp theta
      have hdRealPos : (0 : ℝ) < d := by exact_mod_cast hdPos
      have hThetaPos : 0 < theta := by
        dsimp [theta]
        positivity
      have hThetaLe : theta ≤ Real.pi := by
        dsimp [theta]
        rw [div_le_iff₀ hdRealPos]
        have hdRealTwo : (2 : ℝ) ≤ d := by exact_mod_cast hdTwo
        nlinarith [Real.pi_pos]
      have hzPow : z ^ d = 1 := by
        change Circle.exp theta ^ d = 1
        rw [← Circle.exp_natCast_mul]
        have hAngle : (d : ℝ) * theta = 2 * Real.pi := by
          dsimp [theta]
          field_simp
        rw [hAngle, Circle.exp_two_pi]
      have hzOne : z = 1 := h z hzPow
      have hArgZero : Complex.arg z = 0 := Circle.arg_eq_zero.mpr hzOne
      have hArgTheta : Complex.arg z = theta := by
        apply Circle.arg_exp
        · linarith [Real.pi_pos]
        · exact hThetaLe
      linarith
  · rintro rfl z hz
    simpa using hz

/-- A circle in the two-torus is faithful exactly when its two integer
exponents form a primitive pair. -/
theorem circlePairPowerHom_injective_iff (mn : ℤ × ℤ) :
    Function.Injective (circlePairPowerHom mn) ↔
      mn.1.gcd mn.2 = 1 := by
  constructor
  · intro hInject
    apply (forall_pow_eq_one_imp_eq_one_iff (mn.1.gcd mn.2)).mp
    intro z hz
    have hPowers : z ^ mn.1 = 1 ∧ z ^ mn.2 = 1 :=
      pow_intGCD_eq_one.mp hz
    apply hInject
    apply Prod.ext
    · simpa using hPowers.1
    · simpa using hPowers.2
  · intro hGcd z w hzw
    have hm : z ^ mn.1 = w ^ mn.1 := congrArg Prod.fst hzw
    have hn : z ^ mn.2 = w ^ mn.2 := congrArg Prod.snd hzw
    have hDivM : (z / w) ^ mn.1 = 1 := by
      rw [div_zpow, hm]
      simp
    have hDivN : (z / w) ^ mn.2 = 1 := by
      rw [div_zpow, hn]
      simp
    have hDivGcd : (z / w) ^ mn.1.gcd mn.2 = 1 :=
      pow_intGCD_eq_one.mpr ⟨hDivM, hDivN⟩
    rw [hGcd, pow_one] at hDivGcd
    exact div_eq_one.mp hDivGcd

end

end CircleHomLattice
end Math
