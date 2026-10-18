module

public import Mathlib.Algebra.Lie.Basis.Prod
import all Mathlib.Algebra.Lie.Basis.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Comparing a based Lie algebra with a simple algebra

Mathlib's `LieAlgebra.Basis.prodEquivLeft` supplies the projection equivalence.
Only the target needs to be simple: the diagonal generated product projects
isomorphically to the source. An equal-dimension check then gives an
isomorphism to the target, preserving the specified generators.

The pinned internal helper already requires only target simplicity. We reuse it
directly rather than maintaining an adapted projection-kernel proof. The public
`equivOfReindex` instead requires both algebras to be simple; the local wrapper
uses equal dimensions to avoid that source-side prerequisite.
-/

set_option autoImplicit false

namespace Math.BasedLieComparison

noncomputable section

open Function LieAlgebra LieAlgebra.Basis LieSubalgebra Set

variable {ι L₁ L₂ K : Type*} [Finite ι] [Field K] [CharZero K]
  [LieRing L₁] [LieAlgebra K L₁] [FiniteDimensional K L₁]
  [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L₂] [IsSimple K L₂]
  {H₁ : LieSubalgebra K L₁} {H₂ : LieSubalgebra K L₂}
  (b₁ : LieAlgebra.Basis ι H₁) (b₂ : LieAlgebra.Basis ι H₂) (hA : b₁.A = b₂.A)

include hA in
theorem injective_fst_prod :
    Injective ((LieHom.fst K L₁ L₂).comp (b₁.prod (Equiv.refl ι) b₂).incl) := by
  exact (prodEquivLeft (Equiv.refl ι) b₁ b₂ (by simpa using hA)).injective

def leftEquiv : b₁.prod (Equiv.refl ι) b₂ ≃ₗ⁅K⁆ L₁ :=
  prodEquivLeft (Equiv.refl ι) b₁ b₂ (by simpa using hA)

public def toSimple : L₁ →ₗ⁅K⁆ L₂ :=
  ((LieHom.snd K L₁ L₂).comp (b₁.prod (Equiv.refl ι) b₂).incl).comp
    (leftEquiv b₁ b₂ hA).symm.toLieHom

public theorem toSimple_surjective : Surjective (toSimple b₁ b₂ hA) :=
  (surjective_snd_prod (Equiv.refl ι) b₁ b₂).comp (leftEquiv b₁ b₂ hA).symm.surjective

@[simp] public theorem toSimple_h (i : ι) : toSimple b₁ b₂ hA (b₁.h i) = b₂.h i := by
  have h := (leftEquiv b₁ b₂ hA).symm_apply_apply (prodH (Equiv.refl ι) b₁ b₂ i)
  exact congrArg (fun x : b₁.prod (Equiv.refl ι) b₂ => (x : L₁ × L₂).2) h

@[simp] public theorem toSimple_e (i : ι) : toSimple b₁ b₂ hA (b₁.e i) = b₂.e i := by
  have h := (leftEquiv b₁ b₂ hA).symm_apply_apply (prodE (Equiv.refl ι) b₁ b₂ i)
  exact congrArg (fun x : b₁.prod (Equiv.refl ι) b₂ => (x : L₁ × L₂).2) h

@[simp] public theorem toSimple_f (i : ι) : toSimple b₁ b₂ hA (b₁.f i) = b₂.f i := by
  have h := (leftEquiv b₁ b₂ hA).symm_apply_apply (prodF (Equiv.refl ι) b₁ b₂ i)
  exact congrArg (fun x : b₁.prod (Equiv.refl ι) b₂ => (x : L₁ × L₂).2) h

/-- Matching bases, target simplicity, and equal dimensions suffice. -/
public def equiv (hd : Module.finrank K L₁ = Module.finrank K L₂) : L₁ ≃ₗ⁅K⁆ L₂ :=
  .ofBijective (toSimple b₁ b₂ hA)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
      (toSimple_surjective b₁ b₂ hA), toSimple_surjective b₁ b₂ hA⟩

@[simp] public theorem equiv_h (hd) (i : ι) : equiv b₁ b₂ hA hd (b₁.h i) = b₂.h i :=
  toSimple_h b₁ b₂ hA i

@[simp] public theorem equiv_e (hd) (i : ι) : equiv b₁ b₂ hA hd (b₁.e i) = b₂.e i :=
  toSimple_e b₁ b₂ hA i

@[simp] public theorem equiv_f (hd) (i : ι) : equiv b₁ b₂ hA hd (b₁.f i) = b₂.f i :=
  toSimple_f b₁ b₂ hA i

end

end Math.BasedLieComparison
