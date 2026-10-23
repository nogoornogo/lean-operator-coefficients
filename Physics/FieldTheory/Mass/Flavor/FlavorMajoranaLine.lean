import Physics.FieldTheory.Yukawa.Actions.FlavorStabilizer
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-! Exact residual flavor symmetry of a specified symmetric coefficient on
one complex line, with a zero-VEV accidental-symmetry control. -/
namespace Physics.FlavorMajoranaLine
set_option autoImplicit false
noncomputable section
open FlavorStabilizer

def phaseAction : Representation ℂ Circle ℂ where
  toFun z := (z : ℂ) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' z w := by
    apply LinearMap.ext
    intro x
    change (↑(z * w) : ℂ) * x = (z : ℂ) * ((w : ℂ) * x)
    rw [Circle.coe_mul, mul_assoc]

def form (c : ℂ) : LinearMap.BilinForm ℂ ℂ := c • LinearMap.mul ℂ ℂ

theorem form_symmetric (c : ℂ) : (form c).IsSymm := by
  constructor
  intro x y
  change c * (x * y) = c * (y * x)
  rw [mul_comm x y]

def subgroup (c : ℂ) : Subgroup Circle := massSubgroup phaseAction (form c)

theorem mem_iff (c : ℂ) (z : Circle) : z ∈ subgroup c ↔ c = 0 ∨ z ^ 2 = 1 := by
  rw [subgroup, mass_mem_iff]
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have he : c * (z : ℂ) ^ 2 = c * 1 := by
        simpa [form, phaseAction, mul_assoc, pow_two] using h 1 1
      have hz := mul_left_cancel₀ hc he
      apply Circle.coe_injective
      simpa only [Circle.coe_pow, Circle.coe_one] using hz
  · rintro (rfl | hz) x y
    · simp [form]
    · have he : (z : ℂ) ^ 2 = 1 := by
        simpa only [Circle.coe_pow, Circle.coe_one] using
          congrArg (fun w : Circle => (w : ℂ)) hz
      change c * ((z : ℂ) * x * ((z : ℂ) * y)) = c * (x * y)
      calc
        _ = c * ((z : ℂ) ^ 2) * (x * y) := by ring
        _ = _ := by rw [he, mul_one]

theorem zero_subgroup : subgroup 0 = ⊤ := by ext z; simp [mem_iff]

theorem nonzero_subgroup (c : ℂ) (hc : c ≠ 0) :
    subgroup c = (powMonoidHom (α := Circle) 2).ker := by
  ext z
  simp [mem_iff, hc, MonoidHom.mem_ker]

def rootsHom (c : ℂ) (hc : c ≠ 0) : subgroup c →* rootsOfUnity 2 Circle where
  toFun z := rootsOfUnity.mkOfPowEq z.val ((mem_iff c z.val).mp z.property |>.resolve_left hc)
  map_one' := rootsOfUnity.coe_injective rfl
  map_mul' _ _ := rootsOfUnity.coe_injective rfl

theorem rootsHom_bijective (c : ℂ) (hc : c ≠ 0) : Function.Bijective (rootsHom c hc) := by
  constructor
  · intro z w h
    apply Subtype.ext
    exact congrArg (fun r : rootsOfUnity 2 Circle => (r.val : Circle)) h
  · intro r
    have hr : (r.val : Circle) ^ 2 = 1 := (mem_rootsOfUnity' _ _).mp r.property
    exact ⟨⟨r.val, (mem_iff c _).mpr (Or.inr hr)⟩, rootsOfUnity.coe_injective rfl⟩

def cyclicRootsEquiv : Multiplicative (ZMod 2) ≃* rootsOfUnity 2 Circle :=
  MulEquiv.ofBijective (ZMod.rootsOfUnityAddChar 2).toMonoidHom
    (bijective_rootsOfUnityAddChar 2)

def cyclicEquiv (c : ℂ) (hc : c ≠ 0) : subgroup c ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective (rootsHom c hc) (rootsHom_bijective c hc)).trans cyclicRootsEquiv.symm

theorem nonzero_card (c : ℂ) (hc : c ≠ 0) : Nat.card (subgroup c) = 2 := by
  rw [Nat.card_congr (cyclicEquiv c hc).toEquiv]
  simp

def coupling (c : ℂ) : ℂ →ₗ[ℂ] LinearMap.BilinForm ℂ ℂ :=
  LinearMap.toSpanSingleton ℂ _ (form c)

@[simp] theorem coupling_evaluation (c v : ℂ) : coupling c v = form (c * v) := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  change v * (c * (x * y)) = (c * v) * (x * y)
  ring

theorem coupling_subgroup (c : ℂ) :
    couplingSubgroup (Representation.trivial ℂ Circle ℂ) phaseAction (coupling c) =
      subgroup c := by
  ext z
  rw [coupling_mem_iff, subgroup, mass_mem_iff]
  constructor
  · intro h x y
    simpa [coupling] using h 1 x y
  · intro h s x y
    change s * (form c (phaseAction z x) (phaseAction z y)) = s * form c x y
    rw [h]

theorem evaluated_subgroup (c v : ℂ) :
    massSubgroup phaseAction (coupling c v) = subgroup (c * v) := by
  rw [coupling_evaluation]
  rfl

theorem nonzero_vacuum (c v : ℂ) (hv : v ≠ 0) :
    massSubgroup phaseAction (coupling c v) =
      couplingSubgroup (Representation.trivial ℂ Circle ℂ) phaseAction (coupling c) := by
  rw [evaluated_subgroup, coupling_subgroup]
  ext z
  simp [mem_iff, mul_eq_zero, hv]

theorem zero_vacuum : massSubgroup phaseAction (coupling 1 0) = ⊤ := by
  rw [evaluated_subgroup]
  simpa using zero_subgroup

/-- Vanishing evaluation can strictly enlarge symmetry without erasing the coupling. -/
theorem accidental_strict :
    couplingSubgroup (Representation.trivial ℂ Circle ℂ) phaseAction (coupling 1) ≠
      massSubgroup phaseAction (coupling 1 0) := by
  rw [coupling_subgroup, zero_vacuum]
  intro h
  have hi : Circle.exp (Real.pi / 2) ∈ subgroup 1 := by rw [h]; trivial
  have hz := ((mem_iff 1 _).mp hi).resolve_left one_ne_zero
  have he : Circle.exp (Real.pi / 2) ^ 2 = Circle.exp Real.pi := by
    rw [← Circle.exp_natCast_mul]
    congr 1
    ring
  rw [he] at hz
  exact Circle.exp_pi_ne_one hz

end
end Physics.FlavorMajoranaLine
