import Math.RepresentationTheory.Symmetric.SymmetricFourth22
import Math.RepresentationTheory.Color.Diagrams.DefiningTraceFreeProduct
import Math.RepresentationTheory.Color.SU3.SU3ColorPair
import Math.RepresentationTheory.Color.SU3.SU3DualExterior

/-! Actual color factors required by quartic Q branching. All source
equivalences and contraction kernels are constructed, without a Young
branching or irreducibility premise. -/
namespace Math.SU3QuarticColor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
open SU3DefiningExterior
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

abbrev harmonic := SymmetricSquareContractionRepresentation.action rho
abbrev dualHarmonic := SymmetricSquareContractionRepresentation.action rho.dual

theorem harmonic_nontrivial : Nontrivial (SymmetricSquareContraction.Kernel (A := Vector)) := by
  obtain ⟨x, hx⟩ := SymmetricSquareContraction.exists_kernel_ne_zero (A := Vector)
    (Pi.single (0 : Fin 3) (1 : ℂ)) (LinearMap.proj (1 : Fin 3))
    (by intro h; have hz := congrFun h 0; simp at hz)
    (by intro h; have hz := DFunLike.congr_fun h (Pi.single (1 : Fin 3) 1); simp at hz)
    (by simp)
  exact ⟨⟨x, 0, hx⟩⟩

theorem dualHarmonic_nontrivial :
    Nontrivial (SymmetricSquareContraction.Kernel (A := Module.Dual ℂ Vector)) := by
  obtain ⟨x, hx⟩ := SymmetricSquareContraction.exists_kernel_ne_zero (A := Module.Dual ℂ Vector)
    (LinearMap.proj (0 : Fin 3))
    (Module.Dual.eval ℂ Vector (Pi.single (1 : Fin 3) 1))
    (by intro h; have hz := DFunLike.congr_fun h (Pi.single (0 : Fin 3) 1); simp at hz)
    (by intro h; have hz := DFunLike.congr_fun h (LinearMap.proj (1 : Fin 3)); simp at hz)
    (by simp)
  exact ⟨⟨x, 0, hx⟩⟩

def symmetricSquareSquare : Representation.Equiv
    ((rho.symmetricPower 2).symmetricPower 2)
    ((rho.symmetricPower 4).prod (rho.dual.symmetricPower 2)) :=
  (SymmetricFourth22Representation.equivalence rho).trans
    (prodEquiv (.refl _) ((SymmetricFourth22Representation.kernelFull rho
      (by rw [dimension]; decide)).trans (twoEquiv.symmetricPower 2)))

def dualSymmetricSquareSquare : Representation.Equiv
    ((rho.dual.symmetricPower 2).symmetricPower 2)
    ((rho.dual.symmetricPower 4).prod (rho.symmetricPower 2)) :=
  (SymmetricFourth22Representation.equivalence rho.dual).trans
    (prodEquiv (.refl _) ((SymmetricFourth22Representation.kernelFull rho.dual
      (by rw [Subspace.dual_finrank_eq, dimension]; decide)).trans
        (SU3DualExterior.twoEquiv.symmetricPower 2)))

def definingAdjoint : Representation.Equiv (rho.tprod SU3ColorPair.adjoint)
    (harmonic.prod ((rho.dual.symmetricPower 2).prod rho)) :=
  DefiningTraceFreeProduct.equivalence rho SU3ColorPair.dimension_nonzero
    twoEquiv SU3DualExterior.twoEquiv

def dualDefiningAdjoint : Representation.Equiv
    (rho.dual.tprod (TraceEndomorphismSplit.traceFreeAction rho.dual))
    (dualHarmonic.prod ((rho.symmetricPower 2).prod rho.dual)) :=
  (DefiningTraceFreeProduct.equivalence rho.dual
    (by rw [Subspace.dual_finrank_eq, dimension]; decide)
    (SU3DualExterior.twoEquiv.trans (bidualEquiv rho))
    (((bidualEquiv rho).symm.exteriorPower 2).trans twoEquiv)).trans
      (prodEquiv (.refl _)
        (prodEquiv ((bidualEquiv rho).symm.symmetricPower 2) (.refl _)))

end
end Math.SU3QuarticColor
