import Math.RepresentationTheory.BinaryPatternExterior
import Math.RepresentationTheory.PatternCoefficientSupport

/-! Two-species exterior decomposition preserves supported invariant coefficients. -/
namespace Math.BinaryPatternCoefficient
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {S G Y : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  [AddCommGroup Y] [Module ℂ Y]
  (r : ∀ s, Representation ℂ G (V s)) (s t : S) (n m : ℕ)
  (b : Representation ℂ G Y)

def withSpectator (hst : s ≠ t) :
    Representation.Equiv ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)).tprod b)
      ((PatternExteriorSource.representation r (BinaryPatternExterior.pattern s t n m)).tprod b) where
  toLinearEquiv := TensorProduct.congr (BinaryPatternExterior.linearEquiv r s t n m hst)
    (LinearEquiv.refl ℂ Y)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change BinaryPatternExterior.forward r s t n m
      ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)) g x) ⊗ₜ[ℂ] b g y =
      (PatternExteriorSource.representation r (BinaryPatternExterior.pattern s t n m)) g
        (BinaryPatternExterior.forward r s t n m x) ⊗ₜ[ℂ] b g y
    exact congrArg (fun z => z ⊗ₜ[ℂ] b g y)
      (LinearMap.congr_fun ((BinaryPatternExterior.equiv r s t n m hst).isIntertwining' g) x)

/-- This transports the entire coefficient space, including arbitrary residual actions. -/
def equiv (hst : s ≠ t) :
    PatternCoefficientSupport.space r (BinaryPatternExterior.pattern s t n m) b ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants
        ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)).tprod b) :=
  (PatternCoefficientSupport.equiv r _ b).trans
    (InvariantCoefficientTransport.alongEquiv (withSpectator r s t n m b hst)).symm

end
end Math.BinaryPatternCoefficient
