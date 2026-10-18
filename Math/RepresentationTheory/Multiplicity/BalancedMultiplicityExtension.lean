import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex

/-! Spectral certificates for adding the same residual representation to
both sides of a species index. No compactness is needed for cancellation. -/

namespace Math.BalancedMultiplicityExtension
noncomputable section
open Representation ProductFactorization

variable {G H E F U : Type*} [Group G] [Group H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (tau : Representation ℂ (G × H) E) (base : Representation ℂ (G × H) F)
  (r : Representation ℂ G U)

/-- The extra representation must agree including H, not just in dimension.
Coordinates for the finite additional space do not prescribe its H action. -/
structure Extension where
  dimension : ℕ
  extra : Representation ℂ H (Fin dimension → ℂ)
  positive : Equiv (multiplicityRepresentation tau r)
    ((multiplicityRepresentation base r).prod extra)
  negative : Equiv (multiplicityRepresentation tau r.dual).dual
    (((multiplicityRepresentation base r.dual).dual).prod extra)

theorem character_prod {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (a : Representation ℂ H V) (b : Representation ℂ H W)
    (h : H) : (a.prod b).character h = a.character h + b.character h :=
  LinearMap.trace_prodMap' (a h) (b h)

omit [FiniteDimensional ℂ E] in
theorem index_eq [TopologicalSpace H] (e : Extension tau base r) (h : H) :
    CompactMultiplicityIndex.index tau r h = CompactMultiplicityIndex.index base r h := by
  unfold CompactMultiplicityIndex.index
  rw [char_iso e.positive, char_iso e.negative,
    character_prod, character_prod]
  ring

def refl : Extension tau tau r where
  dimension := 0
  extra := 1
  positive := {
    toLinearEquiv := (LinearEquiv.prodUnique (R := ℂ)
      (M := MultiplicitySpace tau r) (M₂ := Fin 0 → ℂ)).symm
    isIntertwining' h := by
      apply LinearMap.ext; intro f
      exact Prod.ext rfl (Subsingleton.elim _ _) }
  negative := {
    toLinearEquiv := (LinearEquiv.prodUnique (R := ℂ)
      (M := Module.Dual ℂ (MultiplicitySpace tau r.dual)) (M₂ := Fin 0 → ℂ)).symm
    isIntertwining' h := by
      apply LinearMap.ext; intro f
      exact Prod.ext rfl (Subsingleton.elim _ _) }

omit [FiniteDimensional ℂ E] in
theorem negative_finrank (e : Extension tau base r) :
    Module.finrank ℂ (MultiplicitySpace tau r.dual) =
      Module.finrank ℂ (MultiplicitySpace base r.dual) + e.dimension := by
  have he := e.negative.toLinearEquiv.finrank_eq
  simpa using he

theorem opposite_nonzero (e : Extension tau base r) (he : 0 < e.dimension) :
    Nontrivial (MultiplicitySpace tau r.dual) := by
  apply (Module.finrank_pos_iff (R := ℂ)).mp
  rw [negative_finrank tau base r e]
  omega

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [FiniteDimensional ℂ F'] (base' : Representation ℂ (G × H) F')

omit [FiniteDimensional ℂ E] in
theorem index_eq_trans [TopologicalSpace H]
    (e : Extension tau base r) (f : Extension base base' r) (h : H) :
    CompactMultiplicityIndex.index tau r h = CompactMultiplicityIndex.index base' r h :=
  (index_eq tau base r e h).trans (index_eq base base' r f h)

end
end Math.BalancedMultiplicityExtension
