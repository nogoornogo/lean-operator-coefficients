import Math.RepresentationTheory.Relations.FiniteStatisticsQuotient
import TauCeti.RepresentationTheory.Tensor.Power
import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
import TauCeti.RepresentationTheory.Symmetric.SignCharacter

/-! Arbitrary-slot tensor statistics with arbitrary residual flavor action. -/
namespace Math.TensorPermutationStatistics
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H F : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ H F) (d : ℕ)

abbrev permutation := PiTensorProduct.reindexRepresentation ℂ F (Fin d)

theorem commutes (g : Equiv.Perm (Fin d)) (h : H) (u : ⨂[ℂ]^d F) :
    permutation (F := F) d g (a.tensorPower d h u) =
      a.tensorPower d h (permutation (F := F) d g u) := by
  have he := PiTensorProduct.commute_reindexRepresentation_map ℂ F (Fin d) g (a h)
  exact congrArg (fun f : Module.End ℂ (⨂[ℂ]^d F) => f u) he.eq

@[simp] theorem permutation_tprod (g : Equiv.Perm (Fin d)) (v : Fin d → F) :
    permutation d g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => v (g.symm i)) :=
  PiTensorProduct.reindex_tprod g v

-- Explicit instance avoids any finiteness assumption on the flavor module.
local instance cardInvertible : Invertible (Fintype.card (Equiv.Perm (Fin d)) : ℂ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm (Fin d)))

def symmetricQuotientEquiv :=
  FiniteStatisticsQuotient.equiv (a.tensorPower d) (permutation (F := F) d) (commutes a d)

def signCharacter := TauCeti.signLinearCharacter ℂ (Fin d)

def alternatingQuotientEquiv :=
  FiniteStatisticsQuotient.characterEquiv (a.tensorPower d) (permutation (F := F) d)
    (commutes a d) (signCharacter d)

theorem alternating_condition (u : ⨂[ℂ]^d F) :
    u ∈ (FiniteStatisticsQuotient.twisted (permutation (F := F) d) (signCharacter d)).invariants ↔
      ∀ g : Equiv.Perm (Fin d), permutation d g u = (signCharacter d g).val • u :=
  FiniteStatisticsQuotient.mem_twisted _ _ _

end
end Math.TensorPermutationStatistics
