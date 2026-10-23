import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFiniteData

/-! The forward matrix is defined by these actual-source orbit words.
An independent stepping cache and its entry checker are no longer needed. -/
namespace Physics.LiSixQuarkCertificate
noncomputable section
def columnR (j : Fin 25) (p q : Fin 5) : ℚ :=
  basisRational ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q)) j

theorem orbit_column (j : Fin 25) : orbitR j = columnR j := by
  ext p q
  simp only [columnR, basisRational, Equiv.symm_apply_apply]

theorem orbitR_agrees (i j : Fin 25) :
    orbitR j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
      ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2 = basisRational i j := rfl

end
end Physics.LiSixQuarkCertificate
