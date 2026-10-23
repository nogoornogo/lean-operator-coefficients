import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.RepresentationTheory.Decomposition.IrreducibilityTransport
import Math.LinearAlgebra.Selection.SelectionCriteria
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Gluing nonzero coefficients through an injective boson coupling.
Irreducibility gives surjective curried maps, so restriction to the desired
coupling cannot accidentally vanish. No source singlet premise is imposed. -/
namespace Math.InvariantCoefficientGluing
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G A D B C T : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
  [AddCommGroup T] [Module ℂ T] [Nontrivial T]
  (a : Representation ℂ G A) (d : Representation ℂ G D)
  (b : Representation ℂ G B) (c : Representation ℂ G C) (t : Representation ℂ G T)
  [IsIrreducible b.dual] [IsIrreducible c.dual]

theorem allowed (hf : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b)))
    (hg : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (d.tprod c)))
    (k : IntertwiningMap t (b.tprod c)) (hk : Function.Injective k) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants ((a.tprod d).tprod t)) := by
  obtain ⟨f,hf⟩ := hf
  obtain ⟨g,hg⟩ := hg
  let f' := InvariantTensorCurry.equiv a b f
  let g' := InvariantTensorCurry.equiv d c g
  have hf' : f'≠0 := by
    intro hz
    apply hf
    apply (InvariantTensorCurry.equiv a b).injective
    simpa [f'] using hz
  have hg' : g'≠0 := by
    intro hz
    apply hg
    apply (InvariantTensorCurry.equiv d c).injective
    simpa [g'] using hz
  have hfs : Function.Surjective f' := (IsIrreducible.surjective_or_eq_zero f').resolve_right hf'
  have hgs : Function.Surjective g' := (IsIrreducible.surjective_or_eq_zero g').resolve_right hg'
  let h := (SplitRepresentationProjection.dualMap k).comp
    ((InvariantTensorCurry.tensorDual b c).toIntertwiningMap.comp (f'.tensor g'))
  have hs : Function.Surjective h :=
    (LinearMap.dualMap_surjective_of_injective hk).comp
      ((InvariantTensorCurry.tensorDual b c).surjective.comp
        (TensorProduct.map_surjective hfs hgs))
  have hn : h≠0 := by
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (0 : T)
    obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    obtain ⟨y,hy⟩ := hs phi
    have he := DFunLike.congr_fun hz y
    rw [hy] at he
    have hh := LinearMap.congr_fun he x
    rw [hphi] at hh
    exact one_ne_zero hh
  exact (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv (a.tprod d) t)).mpr ⟨h,hn⟩

end
end Math.InvariantCoefficientGluing
