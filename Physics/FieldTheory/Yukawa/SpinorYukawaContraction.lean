import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.FieldTheory.Yukawa.TwoSpeciesExteriorYukawa

/-! Add the left-Weyl epsilon and descend a distinct-species Yukawa to degree two. -/
namespace GUT.SpinorYukawaContraction
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor
open scoped TensorProduct
variable {G A B S : Type*} [Group G]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup S] [Module ℂ S]
  (a : Representation ℂ G A) (b : Representation ℂ G B) (s : Representation ℂ G S)

def scalarEquiv : Equiv (s.comp (MonoidHom.fst G WeylSpinor.Group))
    (external s (trivial ℂ WeylSpinor.Group ℂ)) :=
  .mk (TensorProduct.rid ℂ S).symm (by intro g; ext v; rfl)

def regroup : Equiv
    (((external a WeylSpinor.left).tprod (external b WeylSpinor.left)).tprod
      (s.comp (MonoidHom.fst G WeylSpinor.Group)))
    (external ((a.tprod b).tprod s) (WeylSpinor.left.tprod WeylSpinor.left)) :=
  (tensorEquiv (regroupPair a b WeylSpinor.left WeylSpinor.left) (scalarEquiv s)).trans
    ((regroupPair (a.tprod b) s (WeylSpinor.left.tprod WeylSpinor.left)
      (trivial ℂ WeylSpinor.Group ℂ)).trans
      (externalEquiv (Representation.Equiv.refl _) (Representation.TensorProduct.rid ℂ _)))

def ordered (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ G ℂ)) :=
  (coefficient f WeylSpinor.epsilonLeft).comp (regroup a b s).toIntertwiningMap

@[simp] theorem ordered_apply
    (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ G ℂ))
    (x : A) (y : B) (h : S) (u v : WeylSpinor.Space) :
    ordered a b s f (((x ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] v)) ⊗ₜ[ℂ] h) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] h) * SMEpsilonTensor.eps2 u v := by
  simp [ordered,regroup,Representation.Equiv.trans,scalarEquiv,
    tensorEquiv,regroupPair,externalEquiv,SplitRepresentationProjection.restrictEquiv,
    ExternalInvariantTensor.coefficient,WeylSpinor.epsilonLeft,SMEpsilonTensor.weakTensor,
    SMEpsilonTensor.eps2Bilin]

def exterior (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ G ℂ)) :=
  TwoSpeciesExteriorYukawa.coefficient (external a WeylSpinor.left)
    (external b WeylSpinor.left) (s.comp (MonoidHom.fst G WeylSpinor.Group))
    (ordered a b s f)

theorem exterior_nonzero
    (f : IntertwiningMap ((a.tprod b).tprod s) (trivial ℂ G ℂ))
    (x : A) (y : B) (h : S) (hf : f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] h) ≠ 0) :
    exterior a b s f ≠ 0 := by
  apply TwoSpeciesExteriorYukawa.nonzero _ _ _ _
    (x ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 0)
    (y ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 1) h
  simpa [ordered_apply,SMEpsilonTensor.eps2,SMEpsilonTensor.weakBasis] using hf
end
end GUT.SpinorYukawaContraction
