import Math.RepresentationTheory.CommutingStatisticsModule
import Math.RepresentationTheory.RelationQuotient

/-! Isotypic classification after independently specified input relations.
The relation space must be stable under both actions; statistics stability is
an explicit input, not inferred from residual stability. -/
namespace Math.RelationStatisticsIsotypic
set_option autoImplicit false
noncomputable section
open Representation
variable {k H S U W : Type*} [Field k] [Group H] [Group S]
  [Finite S] [NeZero (Nat.card S : k)]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (rho : Representation k H U) (b : Representation k S U)
  (commutes : ∀ g h u, b g (rho h u) = rho h (b g u))
  (R : Submodule k U) (hR : ∀ h, R ≤ R.comap (rho h))
  (sR : ∀ g, R ≤ R.comap (b g))

include commutes in
omit [Finite S] [NeZero (Nat.card S : k)] in
theorem quotient_commutes (g : S) (h : H) (u : U ⧸ R) :
    b.quotient R sR g (rho.quotient R hR h u) =
      rho.quotient R hR h (b.quotient R sR g u) := by
  obtain ⟨v, rfl⟩ := R.mkQ_surjective u
  exact congrArg R.mkQ (commutes g h v)

def coefficientEquiv (w : Representation k H W) :
    RelationQuotient.vanishing rho w R ≃ₗ[k]
      (∀ c : CommutingStatisticsModule.Index (b.quotient R sR),
        IntertwiningMap
          (CommutingStatisticsModule.block (rho.quotient R hR) (b.quotient R sR)
            (quotient_commutes rho b commutes R hR sR) c) w) :=
  (RelationQuotient.equiv rho w R hR).trans
    (CommutingStatisticsModule.coefficientEquiv (rho.quotient R hR) (b.quotient R sR)
      (quotient_commutes rho b commutes R hR sR) w)

end
end Math.RelationStatisticsIsotypic
