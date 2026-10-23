import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import Mathlib.LinearAlgebra.Trace
import TauCeti.RepresentationTheory.Subrepresentation
import Math.RepresentationTheory.Decomposition.IrreducibleHomScalar

/-! Equivariant scalar/trace-free endomorphism splitting for a nonzero
finite-dimensional complex representation. No irreducibility or tensor
branching classification is assumed. -/
namespace Math.TraceEndomorphismSplit
set_option autoImplicit false
noncomputable section
open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (rho : Representation ℂ G V)

abbrev action := Representation.linHom rho rho

def trace : IntertwiningMap (action rho) (trivial ℂ G ℂ) where
  toLinearMap := LinearMap.trace ℂ V
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    change LinearMap.trace ℂ V ((rho g)*f*(rho g⁻¹))=LinearMap.trace ℂ V f
    rw [LinearMap.trace_mul_comm,← mul_assoc,← map_mul,inv_mul_cancel,map_one,one_mul]

abbrev traceFree := (trace rho).ker
abbrev TraceFree := (traceFree rho).toSubmodule
abbrev traceFreeAction := (traceFree rho).toRepresentation

def scalar : IntertwiningMap (trivial ℂ G ℂ) (action rho) where
  toLinearMap := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (LinearMap.id : V →ₗ[ℂ] V)
  isIntertwining' g := by
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro x
    change s • x=rho g (s • rho g⁻¹ x)
    rw [map_smul,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl

def project : IntertwiningMap (action rho) (trivial ℂ G ℂ) :=
  (Module.finrank ℂ V : ℂ)⁻¹ • trace rho

variable (hd : Module.finrank ℂ V≠0)

include hd in
theorem project_scalar (s : ℂ) : project rho (scalar rho s)=s := by
  have hdc : (Module.finrank ℂ V : ℂ)≠0 := by exact_mod_cast hd
  change (Module.finrank ℂ V : ℂ)⁻¹ * LinearMap.trace ℂ V (s • LinearMap.id)=s
  rw [map_smul,LinearMap.trace_id,smul_eq_mul]
  field_simp

omit hd [FiniteDimensional ℂ V] in
theorem project_traceFree (x : TraceFree rho) : project rho x.val=0 := by
  have hx : trace rho x.val=0 := x.property
  change (Module.finrank ℂ V : ℂ)⁻¹ * trace rho x.val=0
  rw [hx,mul_zero]

def remainder : IntertwiningMap (action rho) (action rho) :=
  IntertwiningMap.id _-(scalar rho).comp (project rho)

def freePart : IntertwiningMap (action rho) (traceFreeAction rho) where
  toLinearMap := (remainder rho).toLinearMap.codRestrict (TraceFree rho) (by
    intro f
    change trace rho (f-scalar rho (project rho f))=0
    have hdc : (Module.finrank ℂ V : ℂ)≠0 := by exact_mod_cast hd
    change LinearMap.trace ℂ V (f-((Module.finrank ℂ V : ℂ)⁻¹ * LinearMap.trace ℂ V f) • LinearMap.id)=0
    rw [map_sub,map_smul,LinearMap.trace_id,smul_eq_mul]
    field_simp
    ring)
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact (remainder rho).isIntertwining _ _ g f

def assemble : IntertwiningMap ((trivial ℂ G ℂ).prod (traceFreeAction rho)) (action rho) :=
  (scalar rho).comp (IntertwiningMap.fst ℂ _ _)+
    (traceFree rho).subtype.comp (IntertwiningMap.snd ℂ _ _)

omit hd [FiniteDimensional ℂ V] in
theorem assemble_apply (x : ℂ × TraceFree rho) : assemble rho x=scalar rho x.1+x.2.val := rfl

include hd in
theorem assemble_surjective : Function.Surjective (assemble rho) := by
  intro f
  refine ⟨(project rho f,freePart rho hd f),?_⟩
  change scalar rho (project rho f)+(f-scalar rho (project rho f))=f
  rw [← add_sub_assoc,add_comm,add_sub_cancel_right]

include hd in
theorem assemble_injective : Function.Injective (assemble rho) := by
  intro x y h
  have hs := congrArg (project rho) h
  simp only [assemble_apply,map_add,project_scalar rho hd,project_traceFree,add_zero] at hs
  apply Prod.ext hs
  apply Subtype.ext
  rw [assemble_apply,assemble_apply,hs] at h
  exact add_left_cancel h

def equivalence : Representation.Equiv ((trivial ℂ G ℂ).prod (traceFreeAction rho)) (action rho) :=
  (assemble rho).ofBijective ⟨assemble_injective rho hd,assemble_surjective rho hd⟩

include hd in
/-- Schur's lemma excludes fixed trace-free endomorphisms; it does not
assert the whole trace-free representation is irreducible. -/
theorem fixed_traceFree_zero [IsIrreducible rho] (x : TraceFree rho)
    (hx : ∀ g, traceFreeAction rho g x=x) : x=0 := by
  let f : IntertwiningMap rho rho :=
    { toLinearMap := x.val
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        have he := congrArg Subtype.val (hx g)
        have he' := DFunLike.congr_fun he (rho g v)
        change rho g (x.val (rho g⁻¹ (rho g v)))=x.val (rho g v) at he'
        have hv : rho g⁻¹ (rho g v)=v := by
          rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
          rfl
        rw [hv] at he'
        exact he'.symm }
  obtain ⟨s,hs⟩ := IrreducibleHomScalar.scalar_bridge rho rho (.refl rho) f
  have hxs : x.val=s • (LinearMap.id : V →ₗ[ℂ] V) := congrArg IntertwiningMap.toLinearMap hs
  have ht : trace rho x.val=0 := x.property
  change LinearMap.trace ℂ V x.val=0 at ht
  rw [hxs,map_smul,LinearMap.trace_id,smul_eq_mul] at ht
  have hdc : (Module.finrank ℂ V : ℂ)≠0 := by exact_mod_cast hd
  have hs₀ : s=0 := (mul_eq_zero.mp ht).resolve_right hdc
  apply Subtype.ext
  rw [hxs,hs₀,zero_smul]
  rfl

end
end Math.TraceEndomorphismSplit
