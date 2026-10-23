import Physics.StandardModel.Operators.Dipole.DipoleModelInterface
import Math.LinearAlgebra.Constructions.PolynomialBasisCoordinates

open Math

/-! Certified construction from polynomial coupling coordinates. No path
expansion proof is required from the caller; physical matching stays external. -/
namespace Physics.DipolePolynomialAutomation
set_option autoImplicit false
noncomputable section
open Representation DipoleModelInterface

variable {H A B M U V S J K : Type*} [Group H] [Fintype J] [Fintype K]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (m : Representation ℂ H M)
  (model : DipoleCouplingModel.Couplings (X := U) (Y := V) a b m)
  (bu : Module.Basis J ℂ U) (bv : Module.Basis K ℂ V)
  (p : J → MvPolynomial S ℂ) (q : K → MvPolynomial S ℂ)
  (s : S → Set ℂ) (mu : A) (electron : Module.Dual ℂ B)

def register : Registered (X := S → ℂ) a b :=
  ofCouplings a b m model (Set.pi Set.univ s)
    (PolynomialBasisCoordinates.evaluate bu p) (PolynomialBasisCoordinates.evaluate bv q)
    mu electron

theorem residual_expansion (x : S → ℂ) :
    (register a b m model bu bv p q s mu electron).residual x =
    WeightedSelectedPaths.synthesis
      (BilinearSelectedPaths.paths (DipoleCouplingModel.bilinear a b m model) bu bv)
      (fun y i => MvPolynomial.eval y (PolynomialBasisCoordinates.weights p q i)) x :=
  PolynomialBasisCoordinates.expansion bu bv p q (DipoleCouplingModel.bilinear a b m model) x

def certificate (hs : ∀ j, (s j).Infinite) :
    PolynomialCertificate (I := J × K) a b (register a b m model bu bv p q s mu electron) where
  coordinates := s
  infinite := hs
  domain_eq := rfl
  paths := BilinearSelectedPaths.paths (DipoleCouplingModel.bilinear a b m model) bu bv
  weights := PolynomialBasisCoordinates.weights p q
  expansion x _ := residual_expansion a b m model bu bv p q s mu electron x

theorem selected (x : S → ℂ) :
    (register a b m model bu bv p q s mu electron).observe x =
    (electron (model.outgoingB (PolynomialBasisCoordinates.evaluate bv q x)
      (model.propagator (model.incoming (PolynomialBasisCoordinates.evaluate bu p x) mu))),
     electron (model.outgoingW (PolynomialBasisCoordinates.evaluate bv q x)
      (model.propagator (model.incoming (PolynomialBasisCoordinates.evaluate bu p x) mu)))) :=
  DipoleCouplingModel.selected a b m model mu electron _ _

theorem exists_nonzero_iff (hs : ∀ j, (s j).Infinite) :
    (∃ x, (register a b m model bu bv p q s mu electron).NonzeroInput x) ↔
    ∃ d, (certificate a b m model bu bv p q s mu electron hs).grouped d ≠ 0 :=
  (certificate a b m model bu bv p q s mu electron hs).exists_nonzero_iff

end
end Physics.DipolePolynomialAutomation
