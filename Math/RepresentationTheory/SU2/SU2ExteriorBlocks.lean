import Math.RepresentationTheory.Exterior.ExtremeCauchyBlocks
import Math.RepresentationTheory.SU2.WeakDoubletScalars
import Math.RepresentationTheory.Decomposition.ProductIrreducibility

/-! The two Cauchy components used by weak/spin exterior blocks are injective. -/
namespace Math.SU2ExteriorBlocks
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct
variable {A : Type*} [AddCommGroup A] [Module ℂ A] {n : ℕ}

theorem column_injective (basis : Module.Basis (Fin n) ℂ A) :
    Function.Injective (TopExteriorCauchy.map (B := Doublet) basis) := by
  exact TopExteriorCauchy.intertwiner_injective basis (trivial ℂ Group A) doublet
    (by intro g; simp [Representation.trivial]) vector functional functional_vector

abbrev left : Representation ℂ (Group × Group) Doublet := doublet.comp (MonoidHom.fst _ _)
abbrev right : Representation ℂ (Group × Group) Doublet := doublet.comp (MonoidHom.snd _ _)

@[reducible] local instance (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n Doublet ⊗[ℂ] Sym[ℂ]^n Doublet) := inferInstance

instance paired_irreducible (n : ℕ) :
    IsIrreducible ((left.symmetricPower n).tprod (right.symmetricPower n)) := by
  change IsIrreducible (ExternalTensorProduct.externalTprod
    (doublet.symmetricPower n) (doublet.symmetricPower n))
  exact ProductIrreducibility.externalTprod_isIrreducible _ _

def pairFunctional : Module.Dual ℂ (Doublet ⊗[ℂ] Doublet) :=
  functional.comp (TopExteriorCauchy.evaluate functional)

theorem pair_normalized : pairFunctional (vector ⊗ₜ[ℂ] vector) = 1 := by
  simp [pairFunctional, functional_vector]

theorem rowColumn_injective (basis : Module.Basis (Fin n) ℂ A) :
    Function.Injective ((TopExteriorCauchy.map (B := Doublet ⊗[ℂ] Doublet) basis).comp
      (SymmetricCauchy.map n)) := by
  exact ExtremeCauchyBlocks.injective basis
    (trivial ℂ (Group × Group) A) left right
    (by intro g; simp [Representation.trivial]) vector vector pairFunctional pair_normalized

end
end Math.SU2ExteriorBlocks
