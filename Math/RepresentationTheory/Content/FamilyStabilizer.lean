import Mathlib.RepresentationTheory.Invariants
import Mathlib.Basic.Complex.Basic

/-! Exact stabilizer of specified vectors in an algebraic representation. -/
namespace Math.FamilyStabilizer
set_option autoImplicit false
noncomputable section
variable {G K V P : Type*} [Group G] [Group K] [AddCommGroup V] [Module ℂ V]

def subgroup (a : Representation ℂ G V) (v : P → V) : Subgroup G where
  carrier := {g | ∀ p, a g (v p) = v p}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by intro p; simp [map_mul, hh p, hg p]
  inv_mem' {g} hg := by
    intro p
    have he := congrArg (a g⁻¹) (hg p)
    simpa using he.symm

@[simp] theorem mem_iff (a : Representation ℂ G V) (v : P → V) (g : G) :
    g ∈ subgroup a v ↔ ∀ p, a g (v p) = v p := Iff.rfl

theorem maximal (a : Representation ℂ G V) (v : P → V) (H : Subgroup G) :
    H ≤ subgroup a v ↔ ∀ g ∈ H, ∀ p, a g (v p) = v p := Iff.rfl

theorem comap (a : Representation ℂ G V) (v : P → V) (q : K →* G) :
    subgroup (a.comp q) v = (subgroup a v).comap q := rfl

theorem zero (a : Representation ℂ G V) : subgroup a (fun _ : P => (0 : V)) = ⊤ := by
  ext g
  simp

def restricted (a : Representation ℂ G V) (v : P → V) :
    Representation ℂ (subgroup a v) V := a.comp (subgroup a v).subtype

theorem restricted_fixed (a : Representation ℂ G V) (v : P → V)
    (g : subgroup a v) (p : P) : restricted a v g (v p) = v p := g.property p

/-- Residual invariant coefficients are actual equivariant linear maps. -/
def invariantHomEquiv {U W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ G V) (v : P → V)
    (b : Representation ℂ (subgroup a v) U)
    (c : Representation ℂ (subgroup a v) W) :
    (b.linHom c).invariants ≃ₗ[ℂ] Representation.IntertwiningMap b c :=
  Representation.invariantsEquivIntertwiningMap b c

end
end Math.FamilyStabilizer
