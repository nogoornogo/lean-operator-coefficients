import Math.Algebra.Variational.LocalEuler
import Math.Algebra.Jets.TwoSidedDifferentialRelations
import Math.RepresentationTheory.Jets.DerivativeInterface

/-! Optional generated EOM inputs. The existing Input operations and published
direct inputs are reused. Symmetry is still an explicit separate certificate. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
variable {F B I : Type*}
@[reducible] local instance : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance : Module ℂ (A F B I) := inferInstance
@[reducible] local instance : Ring (A F B I) := inferInstance

namespace Expr
def seeds (p : Expr F B I) : Set (A F B I) := Set.range p.euler
def equations (p : Expr F B I) : Submodule ℂ (A F B I) := TwoSidedDifferential.relations D p.seeds
def relations (p : Expr F B I) : Submodule ℂ (A F B I) := TwoSidedDifferential.combined D p.seeds

def input {H : Type*} [Group H] (p : Expr F B I) (rho : Representation ℂ H (A F B I))
    (stable : ∀ h, p.relations ≤ p.relations.comap (rho h)) : DerivativeInterface.Input H (A F B I) where
  action := rho
  relations := p.relations
  stable := stable

/-- No symmetry proof is needed when no residual symmetry is requested. -/
def trivialInput (p : Expr F B I) : DerivativeInterface.Input Unit (A F B I) :=
  p.input (Representation.trivial ℂ Unit _) (by intro h; exact le_refl _)

theorem euler_mem (p : Expr F B I) (s : Field F B) : p.euler s ∈ p.equations :=
  TwoSidedDifferential.seed_mem D p.seeds ⟨s, rfl⟩

theorem bulk_mem (p : Expr F B I) (eta : Field F B → A F B I) :
    bulk eta p.euler ∈ p.equations := by
  have h (v : Field F B →₀ A F B I) (hv : ∀ s, v s ∈ p.equations) :
      bulk eta v ∈ p.equations := by
    rw [bulk, Finsupp.lsum_apply]
    apply Submodule.sum_mem
    intro s hs
    exact TwoSidedDifferential.left_mem D p.seeds (eta s) (hv s)
  exact h p.euler (p.euler_mem)

theorem variation_mem (p : Expr F B I) (eta : Field F B → A F B I)
    (h : PreservesParity eta) : p.variation eta ∈ p.relations := by
  rw [p.first_variation eta h]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (p.bulk_mem eta))
    (TwoSidedDifferential.combined_divergence D p.seeds _)

theorem onShell_variation (p : Expr F B I) (eta : Field F B → A F B I)
    (h : PreservesParity eta) : p.trivialInput.projection (p.variation eta) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (p.variation_mem eta h)

theorem first_variation_ibp (p : Expr F B I) (eta : Field F B → A F B I)
    (h : PreservesParity eta) :
    (VariationalIBP.divergence (D (F := F) (B := B) (I := I))).range.mkQ (p.variation eta) =
      (VariationalIBP.divergence D).range.mkQ (bulk eta p.euler) := by
  rw [p.first_variation eta h, map_add]
  have hz : (VariationalIBP.divergence D).range.mkQ
      (VariationalIBP.divergence D (p.boundary eta)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [hz, add_zero]

theorem input_extraction {H : Type*} [Group H] (p : Expr F B I)
    (rho : Representation ℂ H (A F B I)) (stable)
    (f : (p.input rho stable).Coefficient) (u : A F B I) :
    (p.input rho stable).coefficientEquiv f ((p.input rho stable).projection u) = f.val u := rfl

end Expr
end
end Math.LocalPolynomial
