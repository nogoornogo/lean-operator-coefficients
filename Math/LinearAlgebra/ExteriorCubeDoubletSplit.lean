import Math.LinearAlgebra.ExteriorCubeDoublet
import Math.RepresentationTheory.SU2ExteriorBlocks
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Complete cubic doublet branching for a three-dimensional color space.
The two summands have explicit embeddings; their independence is proved
by contraction. Surjectivity uses structural exterior/symmetric dimension
formulas, without a numerical representation certificate. -/
namespace Math.ExteriorCubeDoubletSplit
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open ExteriorCubeHook ExteriorCubeDoublet
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
  (basis : Module.Basis (Fin 3) ℂ A)
abbrev Domain := (Sym[ℂ]^3 B) × (Hook (V := A) ⊗[ℂ] B)
abbrev Total := ⋀[ℂ]^3 (A ⊗[ℂ] B)
@[reducible] local instance : AddCommGroup (Hook (V := A) ⊗[ℂ] B) := inferInstance

theorem contract_column (a : Fin 3 → A) (x : Sym[ℂ]^3 B) :
    contract (TopExteriorCauchy.map a x)=0 := by
  have h : (contract (A := A)).comp (TopExteriorCauchy.map a)=0 := by
    apply SymmetricPurePowers.ext
    intro s
    change contract (TopExteriorCauchy.map a (SymmetricPower.tprod ℂ (fun _ : Fin 3 => s)))=0
    rw [TopExteriorCauchy.diagonal,← cube_eta,contract_cube]
    have he : SU2DoubletDuality.epsilon s s=0 := by
      rw [SU2DoubletDuality.epsilon_apply]
      ring
    simp only [raw_pure,he,zero_smul,sub_self,add_zero]
  exact LinearMap.congr_fun h x

theorem retract_column (x : Sym[ℂ]^3 B) :
    hookRetract (TopExteriorCauchy.map basis x)=0 := by
  change (9 : ℂ)⁻¹ • TensorProduct.map project LinearMap.id
    (contract (TopExteriorCauchy.map basis x))=0
  rw [contract_column,map_zero,smul_zero]

def combine : Domain (A := A) →ₗ[ℂ] Total (A := A) :=
  (TopExteriorCauchy.map basis).comp (LinearMap.fst ℂ _ _)+
    hookInsert.comp (LinearMap.snd ℂ _ _)

theorem combine_injective : Function.Injective (combine basis) := by
  intro x y hxy
  have hs := congrArg hookRetract hxy
  change hookRetract (TopExteriorCauchy.map basis x.1+hookInsert x.2)=
    hookRetract (TopExteriorCauchy.map basis y.1+hookInsert y.2) at hs
  rw [map_add,map_add,retract_column,retract_column,hook_retract_insert,
    hook_retract_insert,zero_add,zero_add] at hs
  apply Prod.ext _ hs
  apply SU2ExteriorBlocks.column_injective basis
  change TopExteriorCauchy.map basis x.1+hookInsert x.2=
    TopExteriorCauchy.map basis y.1+hookInsert y.2 at hxy
  rw [hs] at hxy
  exact add_right_cancel hxy

include basis in
/-- Dimension equality follows from the universal hook splitting and the
standard functor dimension identities for a three-dimensional space.
No color irreducibility or evaluated content rank is an input. -/
theorem dimensions : Module.finrank ℂ (Domain (A := A))=Module.finrank ℂ (Total (A := A)) := by
  let : Module.Finite ℂ A := Module.Finite.of_basis basis
  have ha : Module.finrank ℂ A=3 := by
    rw [Module.finrank_eq_card_basis basis,Fintype.card_fin]
  have he := (ExteriorCubeHook.split (V := A)).finrank_eq
  rw [Module.finrank_tensorProduct,Module.finrank_prod,
    exteriorPower.finrank_eq,exteriorPower.finrank_eq,ha] at he
  change Module.finrank ℂ ((Sym[ℂ]^3 B) × (Hook (V := A) ⊗[ℂ] B))=
    Module.finrank ℂ (⋀[ℂ]^3 (A ⊗[ℂ] B))
  rw [Module.finrank_prod,Module.finrank_tensorProduct,exteriorPower.finrank_eq,
    Module.finrank_tensorProduct,ha,SymmetricPower.finrank_eq]
  norm_num [B,WeakDoubletScalars.Doublet,Nat.multichoose,Nat.choose] at he ⊢
  omega

theorem combine_surjective : Function.Surjective (combine basis) := by
  let : Module.Finite ℂ A := Module.Finite.of_basis basis
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (dimensions basis)).mp
    (combine_injective basis)

/-- The complete middle-degree decomposition, with no unknown Hom premise. -/
def equivalence : Domain (A := A) ≃ₗ[ℂ] Total (A := A) :=
  LinearEquiv.ofBijective (combine basis) ⟨combine_injective basis,combine_surjective basis⟩

end
end Math.ExteriorCubeDoubletSplit
