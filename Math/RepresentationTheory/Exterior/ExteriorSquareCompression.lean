import Math.RepresentationTheory.Exterior.ExteriorSquareCoordinates

/-! Compression of the actual exterior infinitesimal action along a split
inclusion. The compressed matrix is a hypothesis, not a current coefficient. -/
set_option autoImplicit false
namespace Math.ExteriorSquareCoordinates
noncomputable section

theorem compress_infinitesimal {m n : ℕ}
    (i : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (p : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hp : ∀ x, p (i x) = x) (X : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin m) ℂ)
    (hX : ∀ x, p (Matrix.toLin' X (i x)) = Matrix.toLin' Y x) :
    (exteriorPower.map 2 p).comp ((infinitesimal X).comp (exteriorPower.map 2 i)) =
      infinitesimal Y := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext j; fin_cases j <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti]
  change exteriorPower.map 2 p (infinitesimal X
    (exteriorPower.ιMulti ℂ 2 ![i (v 0), i (v 1)])) =
      infinitesimal Y (exteriorPower.ιMulti ℂ 2 ![v 0, v 1])
  rw [infinitesimal_leibniz, map_add, infinitesimal_leibniz]
  simp only [exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti ℂ 2 ![p (Matrix.toLin' X (i (v 0))), p (i (v 1))] +
    exteriorPower.ιMulti ℂ 2 ![p (i (v 0)), p (Matrix.toLin' X (i (v 1)))] = _
  rw [hp, hp, hX, hX]

theorem infinitesimal_zero (n : ℕ) : infinitesimal (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  apply (LinearMap.toMatrix basis basis).injective
  rw [infinitesimal_matrix, map_zero]
  ext a b
  simp [tangent]

end
end Math.ExteriorSquareCoordinates
