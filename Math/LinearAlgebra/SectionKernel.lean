import Mathlib.LinearAlgebra.Prod

/-! An explicit kernel complement from a supplied linear right inverse.
The right inverse is a proved input, not a choice of arbitrary complement. -/
namespace Math.SectionKernel
set_option autoImplicit false
variable {K U V : Type*} [Ring K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  (f : U →ₗ[K] V) (s : V →ₗ[K] U) (h : ∀ v, f (s v)=v)

def project : U →ₗ[K] LinearMap.ker f :=
  (LinearMap.id-s.comp f).codRestrict _ (by
    intro u
    change f (u-s (f u))=0
    rw [map_sub,h,sub_self])

theorem project_kernel (u : LinearMap.ker f) : project f s h u.val=u := by
  apply Subtype.ext
  change u.val-s (f u.val)=u.val
  rw [show f u.val=0 from u.property,map_zero,sub_zero]

theorem project_section (v : V) : project f s h (s v)=0 := by
  apply Subtype.ext
  change s v-s (f (s v))=0
  rw [h,sub_self]

def equivalence : U ≃ₗ[K] V × LinearMap.ker f where
  toLinearMap := f.prod (project f s h)
  invFun v := s v.1+v.2.val
  left_inv u := by
    change s (f u)+(u-s (f u))=u
    rw [add_comm, sub_add_cancel]
  right_inv v := by
    apply Prod.ext
    · change f (s v.1+v.2.val)=v.1
      rw [map_add,h,show f v.2.val=0 from v.2.property,add_zero]
    · change project f s h (s v.1+v.2.val)=v.2
      rw [map_add,project_section,project_kernel,zero_add]

end Math.SectionKernel
