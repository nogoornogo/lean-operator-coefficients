import Math.RepresentationTheory.Characters.AbelianCharacterPolynomial

/-! Coefficients of a finite character polynomial invariant under an
automorphism. No integral weight-lattice model is assumed. -/

set_option autoImplicit false

namespace Math.AbelianActualSpectrum

noncomputable section
variable {G : Type*} [CommGroup G]

theorem coeff_comp_eq_of_eval_invariant (p : Polynomial G) (a : G ≃* G)
    (h : ∀ g, eval p (a g) = eval p g) (chi : G →* ℂ) :
    p (chi.comp a.toMonoidHom) = p chi := by
  let f : (G →* ℂ) → (G →* ℂ) := fun psi => psi.comp a.toMonoidHom
  have hi : Function.Injective f := by
    intro psi phi he
    ext g
    have hh := congrArg (fun k : G →* ℂ => k (a.symm g)) he
    simpa [f] using hh
  have hp : Finsupp.mapDomain f p = p := by
    apply eval_injective
    intro g
    change (Finsupp.mapDomain f p).sum (fun psi n => (n : ℂ) * psi g) = eval p g
    rw [Finsupp.sum_mapDomain_index]
    · exact h g
    · simp
    · intros; simp [add_mul]
  have hc := congrArg (fun q : Polynomial G => q (f chi)) hp
  rw [Finsupp.mapDomain_apply_of_injective hi] at hc
  exact hc.symm

end
end Math.AbelianActualSpectrum
