import Math.RepresentationTheory.CyclicCharge
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace Math.CyclicChargeOrbits
set_option autoImplicit false
variable {k : ℕ} [NeZero k]

def scale (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) : ZMod k × ZMod k :=
  (u*x.1,u*x.2)

omit [NeZero k] in
@[simp] theorem scale_one (x : ZMod k × ZMod k) : scale 1 x = x := by
  simp [scale]

omit [NeZero k] in
@[simp] theorem scale_mul (u v : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    scale u (scale v x) = scale (u*v) x := by simp [scale,mul_assoc]

def Equivalent (x y : ZMod k × ZMod k) : Prop := ∃ u : (ZMod k)ˣ, y = scale u x

omit [NeZero k] in
theorem equivalent_refl (x : ZMod k × ZMod k) : Equivalent x x := ⟨1, by simp⟩
omit [NeZero k] in
theorem equivalent_symm {x y : ZMod k × ZMod k} (h : Equivalent x y) : Equivalent y x := by
  obtain ⟨u,rfl⟩ := h
  exact ⟨u⁻¹, by simp⟩
omit [NeZero k] in
theorem equivalent_trans {x y z : ZMod k × ZMod k}
    (h : Equivalent x y) (h' : Equivalent y z) : Equivalent x z := by
  obtain ⟨u,rfl⟩ := h
  obtain ⟨v,rfl⟩ := h'
  exact ⟨v*u, by simp⟩

def orbit (x : ZMod k × ZMod k) : Finset (ZMod k × ZMod k) :=
  Finset.univ.image (fun u : (ZMod k)ˣ => scale u x)

@[simp] theorem mem_orbit (x y : ZMod k × ZMod k) : y ∈ orbit x ↔ Equivalent x y := by
  simp [orbit,Equivalent,eq_comm]

theorem orbit_eq_iff (x y : ZMod k × ZMod k) : orbit x = orbit y ↔ Equivalent x y := by
  constructor
  · intro h
    have hy : y ∈ orbit y := (mem_orbit y y).mpr (equivalent_refl y)
    rw [← h] at hy
    exact (mem_orbit x y).mp hy
  · intro h
    ext z
    rw [mem_orbit,mem_orbit]
    exact ⟨fun hz => equivalent_trans (equivalent_symm h) hz,
      fun hz => equivalent_trans h hz⟩

omit [NeZero k] in
theorem linear_test (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) (a b : ZMod k) :
    a*(scale u x).1+b*(scale u x).2 = 0 ↔ a*x.1+b*x.2 = 0 := by
  have he : a*(scale u x).1+b*(scale u x).2 = (u : ZMod k)*(a*x.1+b*x.2) := by
    dsimp [scale]; ring
  rw [he,Units.mul_right_eq_zero]

def phaseImage (x : ZMod k × ZMod k) : Finset (ZMod k × ZMod k) :=
  Finset.univ.image (fun g : ZMod k => (x.1*g,x.2*g))
def effectiveOrder (x : ZMod k × ZMod k) : ℕ := (phaseImage x).card

theorem phaseImage_scale (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    phaseImage (scale u x) = phaseImage x := by
  ext z
  simp only [phaseImage,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨(u : ZMod k)*g, ?_⟩
    dsimp [scale]
    congr 1 <;> ring
  · rintro ⟨g,rfl⟩
    refine ⟨(↑u⁻¹ : ZMod k)*g, ?_⟩
    dsimp [scale]
    have hx (a : ZMod k) : (u : ZMod k)*a*((↑u⁻¹ : ZMod k)*g) = a*g := by
      calc
        _ = a*((u : ZMod k)*(↑u⁻¹ : ZMod k))*g := by ring
        _ = a*g := by simp
    exact Prod.ext (hx x.1) (hx x.2)

theorem effectiveOrder_scale (u : (ZMod k)ˣ) (x : ZMod k × ZMod k) :
    effectiveOrder (scale u x) = effectiveOrder x := by
  unfold effectiveOrder
  rw [phaseImage_scale]

noncomputable def phases (x : ZMod k × ZMod k) : ℂ × ℂ :=
  (ZMod.stdAddChar x.1,ZMod.stdAddChar x.2)

theorem phases_injective : Function.Injective (phases (k := k)) := by
  intro x y h
  exact Prod.ext (ZMod.injective_stdAddChar (congrArg Prod.fst h))
    (ZMod.injective_stdAddChar (congrArg Prod.snd h))

theorem effectiveOrder_actual (x : ZMod k × ZMod k) :
    effectiveOrder x = ((phaseImage x).image phases).card := by
  classical
  exact (Finset.card_image_of_injective _ phases_injective).symm

/-- Multiplication by a unit changes the generator of the same cyclic group. -/
def relabel (u : (ZMod k)ˣ) : CyclicCharge.Group k ≃* CyclicCharge.Group k where
  toFun g := Multiplicative.ofAdd ((u : ZMod k)*g.toAdd)
  invFun g := Multiplicative.ofAdd ((↑u⁻¹ : ZMod k)*g.toAdd)
  left_inv g := by change Multiplicative.ofAdd ((↑u⁻¹ : ZMod k)*((u : ZMod k)*g.toAdd)) = g; simp [← mul_assoc]
  right_inv g := by change Multiplicative.ofAdd ((u : ZMod k)*((↑u⁻¹ : ZMod k)*g.toAdd)) = g; simp [← mul_assoc]
  map_mul' g h := by change Multiplicative.ofAdd ((u : ZMod k)*(g.toAdd+h.toAdd)) = _; simp [mul_add]

/-- The two actual field characters are compared at each group element. -/
theorem relabeled_action (u : (ZMod k)ˣ) (q g : ZMod k) :
    CyclicCharge.representation ((u : ZMod k)*q) (Multiplicative.ofAdd g) =
      CyclicCharge.representation q (Multiplicative.ofAdd ((u : ZMod k)*g)) := by
  have h : (u : ZMod k)*q*g = q*((u : ZMod k)*g) := by ring
  change LinearMap.lsmul ℂ ℂ (ZMod.stdAddChar ((u : ZMod k)*q*g)) =
    LinearMap.lsmul ℂ ℂ (ZMod.stdAddChar (q*((u : ZMod k)*g)))
  rw [h]
end Math.CyclicChargeOrbits
