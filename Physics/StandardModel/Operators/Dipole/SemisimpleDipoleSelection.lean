import Physics.StandardModel.Operators.Dipole.DipoleFlavorSelection
import Math.RepresentationTheory.Decomposition.IrreducibleBlockCoordinates

namespace Physics.SemisimpleDipoleSelection
set_option autoImplicit false
noncomputable section
open Math Representation FiniteBlockHom
variable {G I J V W : Type*} [Group G] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, FiniteDimensional ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j))
  [∀ i, IsIrreducible (a i)] [∀ j, IsIrreducible (b j)]
  {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
  (ea : Representation.Equiv rho (action a)) (eb : Representation.Equiv sigma (action b))

def homTransport : IntertwiningMap rho sigma ≃ₗ[ℂ] IntertwiningMap (action a) (action b) where
  toFun f := eb.toIntertwiningMap.comp (f.comp ea.symm.toIntertwiningMap)
  invFun f := eb.symm.toIntertwiningMap.comp (f.comp ea.toIntertwiningMap)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp

def coordinates : IntertwiningMap rho sigma ≃ₗ[ℂ] (IrreducibleBlockCoordinates.Match a b → ℂ) :=
  (homTransport a b ea eb).trans (IrreducibleBlockCoordinates.equiv a b)

def matrixUnit (p : IrreducibleBlockCoordinates.Match a b) : IntertwiningMap rho sigma := by
  classical
  exact (coordinates a b ea eb).symm (Pi.single p 1)

omit [FiniteDimensional ℂ W] in
theorem expansion (f : IntertwiningMap rho sigma) :
    f = ∑ p, (coordinates a b ea eb f p) • matrixUnit a b ea eb p := by
  classical
  have he : coordinates a b ea eb f =
      ∑ p, (coordinates a b ea eb f p) • Pi.single p 1 := by ext t; simp [Pi.single_apply]
  apply (coordinates a b ea eb).injective
  simp only [map_sum,map_smul,matrixUnit,LinearEquiv.apply_symm_apply]
  exact he

theorem selected_allowed_iff (mu : V) (ell : Module.Dual ℂ W) :
    (∃ c : DipoleFlavorSelection.Coefficients rho sigma,
      DipoleFlavorSelection.selector rho sigma mu ell c ≠ 0) ↔
    ∃ p : IrreducibleBlockCoordinates.Match a b, ell (matrixUnit a b ea eb p mu) ≠ 0 := by
  rw [DipoleFlavorSelection.allowed_iff]
  constructor
  · rintro ⟨f,hf⟩
    by_contra hn
    have hz : ∀ p, ell (matrixUnit a b ea eb p mu) = 0 := by simpa using hn
    apply hf
    rw [expansion a b ea eb f]
    simp only [IntertwiningMap.sum_apply,IntertwiningMap.smul_apply,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro p _
    rw [hz p,mul_zero]
  · rintro ⟨p,hp⟩
    exact ⟨matrixUnit a b ea eb p,hp⟩

theorem selected_forbidden_iff (mu : V) (ell : Module.Dual ℂ W) :
    (∀ c : DipoleFlavorSelection.Coefficients rho sigma,
      DipoleFlavorSelection.selector rho sigma mu ell c = 0) ↔
    ∀ p : IrreducibleBlockCoordinates.Match a b, ell (matrixUnit a b ea eb p mu) = 0 := by
  classical
  simpa only [not_exists,not_not] using not_congr (selected_allowed_iff a b ea eb mu ell)
end
end Physics.SemisimpleDipoleSelection
