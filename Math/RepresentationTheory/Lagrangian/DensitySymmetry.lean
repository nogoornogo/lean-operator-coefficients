import Math.Algebra.Variational.EulerNaturality
import Math.RepresentationTheory.Lagrangian.LagrangianModel

/-! Density invariance supplies Euler-span covariance and the full generated
EOM/IBP stability certificate. -/
namespace Math.LocalPolynomial.Prolongation
set_option autoImplicit false
noncomputable section
open CoefficientTransport
variable {F B I : Type*} [Fintype I] (T : Prolongation F B I)

/-- Density invariance is the only Lagrangian-dependent symmetry premise. -/
theorem invariant_euler (p : Expr F B I) (hp : T.algebra p.eval = p.eval) :
    p.euler = push T.fields T.algebra.toLinearMap p.euler :=
  T.euler_natural p p hp.symm

theorem invariant_euler_span (p : Expr F B I) (hp : T.algebra p.eval = p.eval)
    (R : (Field F B →₀ ℂ) ≃ₗ[ℂ] (Field F B →₀ ℂ)) (hR : T.fields = R.toLinearMap)
    (s : Field F B) : T.algebra (p.euler s) ∈ Submodule.span ℂ (Set.range p.euler) := by
  have he := congrArg (push R.symm.toLinearMap (LinearMap.id : A F B I →ₗ[ℂ] A F B I))
    (T.invariant_euler p hp)
  rw [hR] at he
  have hc := push_comp R.toLinearMap R.symm.toLinearMap T.algebra.toLinearMap
    (LinearMap.id : A F B I →ₗ[ℂ] A F B I)
  have hi : R.symm.toLinearMap.comp R.toLinearMap = LinearMap.id := by ext v; simp
  have hev : push R.symm.toLinearMap LinearMap.id p.euler s = T.algebra (p.euler s) := by
    have he' := congrArg (fun v : Field F B →₀ A F B I => v s) he
    simpa only [← LinearMap.comp_apply,hc,hi,LinearMap.id_comp,push_identity_apply,
      AlgHom.toLinearMap_apply] using he'
  rw [← hev,push_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
end
end Math.LocalPolynomial.Prolongation

namespace Math.LagrangianModel.Mixed
set_option autoImplicit false
noncomputable section
open LocalPolynomial
variable {F B I H : Type*} [Group H] [Fintype I]

/-- Package a density with symmetry verified by its evaluated invariance.
All transformation obligations are independent of the density. -/
def ofInvariantDensity (p : Expr F B I) (rho : Representation ℂ H (A F B I))
    (T : H → Prolongation F B I)
    (hA : ∀ g u, (T g).algebra u = rho g u)
    (R : H → (Field F B →₀ ℂ) ≃ₗ[ℂ] (Field F B →₀ ℂ))
    (hR : ∀ g, (T g).fields = (R g).toLinearMap)
    (hp : ∀ g, rho g p.eval = p.eval) : Mixed F B I H :=
  ofEulerSpan p rho
    (fun g u v => by rw [← hA, map_mul,hA,hA])
    (fun g => (T g).directions)
    (fun g i u => by simpa only [hA] using (T g).derivative_map i u)
    (fun g s => by
      rw [← hA]
      apply (T g).invariant_euler_span p (by simpa only [hA] using hp g) (R g) (hR g) s)

end
end Math.LagrangianModel.Mixed
