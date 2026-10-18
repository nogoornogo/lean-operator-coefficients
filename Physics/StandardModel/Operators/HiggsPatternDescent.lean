import Math.RepresentationTheory.TypedSymmetricPatternHom
import Math.RepresentationTheory.TwoBlockSymmetricDescent
import Math.LinearAlgebra.SelectionCriteria
import Physics.StandardModel.Operators.NeutralHiggsPowers

/-! Fixed scalar content in the original full SM field carrier. The exterior
fermion source is retained exactly; no weak-singlet assumption is used. -/
namespace GUT.HiggsPatternDescent
set_option autoImplicit false
noncomputable section
open Math Representation BnvMixedInput DeltaLOneSignedFields
variable {H : Type*} [Group H]
  {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ H (F s))
  (n : ℕ) {m : ℕ} (scalars : Fin m → ScalarSpecies)

abbrev source := (fullRepresentation flavor).exteriorPower n

abbrev Space := TypedSymmetricPatternHom.sourceSpace
  (scalarField (NeutralHiggsPowers.flavor (H := H))) scalars (source flavor n)

abbrev Ordered := TypedSymmetricPatternHom.orderedSpace
  (scalarField (NeutralHiggsPowers.flavor (H := H))) (source flavor n).dual scalars

def equiv : Space flavor n scalars ≃ₗ[ℂ] Ordered flavor n scalars :=
  TypedSymmetricPatternHom.sourceEquiv _ scalars (source flavor n)

@[simp] theorem equiv_apply (f : Space flavor n scalars)
    (w : ∀ i, ScalarField (S := NeutralHiggsPowers.Multiplicity) (scalars i))
    (x : ⋀[ℂ]^n (∀ s, Field (F := F) s)) :
    (equiv flavor n scalars f).val w x =
      f.val (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => Pi.single (scalars i) (w i))) := rfl

theorem allowed_iff : SelectionCriteria.Allowed (Space flavor n scalars) ↔
    SelectionCriteria.Allowed (Ordered flavor n scalars) :=
  SelectionCriteria.allowed_equiv (equiv flavor n scalars)

theorem forbidden_iff : SelectionCriteria.Forbidden (Space flavor n scalars) ↔
    SelectionCriteria.Forbidden (Ordered flavor n scalars) :=
  (SelectionCriteria.ofEquiv (equiv flavor n scalars)).forbidden

end
end GUT.HiggsPatternDescent
