import Math.RepresentationTheory.Lagrangian.BosonicLagrangianInput
import Math.RepresentationTheory.Invariants.TwoSidedCovariance

/-! Euler-span certificates imply stability of the entire generated EOM/IBP
space. The certificate concerns the Euler family of the total density. -/
namespace Math.LocalPolynomial.Expr
set_option autoImplicit false
noncomputable section

variable {F B I H : Type*} [Group H] [Fintype I]

theorem stable_of_euler_span (p : Expr F B I)
    (rho : Representation ℂ H (A F B I))
    (hM : ∀ g u v, rho g (u*v) = rho g u*rho g v)
    (c : H → I → I → ℂ)
    (hD : ∀ g i u, rho g (D i u) = ∑ j, c g i j • D j (rho g u))
    (hE : ∀ g s, rho g (p.euler s) ∈ Submodule.span ℂ (Set.range p.euler)) :
    ∀ g, p.relations ≤ p.relations.comap (rho g) := by
  intro g
  apply TwoSidedCovariance.combined_stable D p.seeds (rho g) (hM g) (c g) (hD g)
  rintro _ ⟨s,rfl⟩
  exact (Submodule.span_le.mpr (fun _ hs => TwoSidedDifferential.seed_mem D p.seeds hs))
    (hE g s)

theorem scalar_stable_of_euler_span (p : Expr Empty B I)
    (rho : Representation ℂ H (Scalar B I))
    (hM : ∀ g u v, rho g (u*v) = rho g u*rho g v)
    (c : H → I → I → ℂ)
    (hD : ∀ g i u, rho g (ScalarJetAlgebra.totalDerivative i u) =
      ∑ j, c g i j • ScalarJetAlgebra.totalDerivative j (rho g u))
    (hE : ∀ g s, rho g (p.scalarEuler s) ∈ Submodule.span ℂ (Set.range p.scalarEuler)) :
    ∀ g, DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds ≤
      (DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds).comap (rho g) := by
  intro g
  rw [← TwoSidedDifferential.commutative_combined]
  apply TwoSidedCovariance.combined_stable
    (fun i => (ScalarJetAlgebra.totalDerivative i).toLinearMap) p.scalarSeeds
    (rho g) (hM g) (c g) (hD g)
  rintro _ ⟨s,rfl⟩
  exact (Submodule.span_le.mpr (fun _ hs => TwoSidedDifferential.seed_mem _ p.scalarSeeds hs))
    (hE g s)

end
end Math.LocalPolynomial.Expr
