import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Schur lemmas and surjective restriction -/

namespace Math.BlockCentralizer
noncomputable section

variable {k G H : Type*} [Field k] [IsAlgClosed k]
variable [Monoid G] [Monoid H]
variable {V₁ V₂ V₃ : Type*}
variable [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
variable [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
variable [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]

omit [IsAlgClosed k] [FiniteDimensional k V₁] [FiniteDimensional k V₂] in
/-- An intertwiner between irreducible finite-dimensional representations of
different dimensions vanishes. -/
theorem intertwiningMap_eq_zero_of_finrank_ne
    {rho : Representation k G V₁} {sigma : Representation k G V₂}
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma]
    (hDimension : Module.finrank k V₁ ≠ Module.finrank k V₂)
    (f : Representation.IntertwiningMap rho sigma) :
    f = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hBijective | hZero
  · exfalso
    apply hDimension
    exact (f.ofBijective hBijective).toLinearEquiv.finrank_eq
  · exact hZero

/-- Schur's lemma over an algebraically closed field, in scalar-action form. -/
theorem intertwiningMap_eq_smul_one_of_irreducible
    (rho : Representation k G V₁) [Representation.IsIrreducible rho]
    (f : Representation.IntertwiningMap rho rho) :
    ∃ c : k, f = c • 1 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rho)).2 f
  exact ⟨c, by simpa using hc.symm⟩

omit [IsAlgClosed k] [FiniteDimensional k V₁] in
/-- Pulling an irreducible representation back along a surjective monoid
homomorphism preserves irreducibility. -/
theorem comp_isIrreducible_of_surjective
    (rho : Representation k G V₁) [Representation.IsIrreducible rho]
    (phi : H →* G) (hphi : Function.Surjective phi) :
    Representation.IsIrreducible (rho.comp phi) := by
  let _ : Nontrivial (Subrepresentation (rho.comp phi)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      apply IsSimpleOrder.bot_ne_top
        (α := Subrepresentation rho)
      apply Subrepresentation.ext
      exact congrArg
        (fun U : Subrepresentation (rho.comp phi) => U.toSubmodule) h⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  let T : Subrepresentation rho :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨h, rfl⟩ := hphi g
        exact S.apply_mem_toSubmodule h hx }
  have hTne : T ≠ ⊥ := by
    intro hT
    apply hS
    apply Subrepresentation.ext
    have hSub : S.toSubmodule = (⊥ : Submodule k V₁) := by
      change T.toSubmodule = (⊥ : Submodule k V₁)
      exact congrArg (fun U : Subrepresentation rho => U.toSubmodule) hT
    exact hSub
  have hTtop : T = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top T).resolve_left hTne
  apply Subrepresentation.ext
  have hSub : S.toSubmodule = (⊤ : Submodule k V₁) := by
    change T.toSubmodule = (⊤ : Submodule k V₁)
    exact congrArg (fun U : Subrepresentation rho => U.toSubmodule) hTtop
  exact hSub

end
end Math.BlockCentralizer
