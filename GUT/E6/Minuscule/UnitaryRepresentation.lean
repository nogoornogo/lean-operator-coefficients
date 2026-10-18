import GUT.E6.Minuscule.SU5Inclusion
import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Mathlib.Analysis.CStarAlgebra.Matrix

open Math

/-! The actual defining action of the compact candidate on the standard
Hilbert 27. No Haar conjugation or group-realization certificate is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GUT.E6.Minuscule

open Math.E6.Minuscule Math.E6
noncomputable section

abbrev Hilbert27 := EuclideanSpace ℂ (Fin 27)

def representation : Representation ℂ compactIdentityComponent Hilbert27 where
  toFun g := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27) (compactMatrix g)).toLinearMap
  map_one' := by simp
  map_mul' g h := by simp

theorem representation_unitary : UnitaryMultiplicity.IsUnitaryRepresentation representation := by
  intro g x y
  change inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27) (compactMatrix g) x)
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27) (compactMatrix g) y) = _
  apply ContinuousLinearMap.inner_map_map_of_mem_unitary
  exact Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27)) g.val.val.property.1

theorem representation_continuous :
    Continuous (fun p : compactIdentityComponent × Hilbert27 => representation p.1 p.2) := by
  change Continuous (fun p : compactIdentityComponent × Hilbert27 =>
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27) (compactMatrix p.1) p.2)
  have hc : Continuous (fun p : compactIdentityComponent × Hilbert27 =>
      (compactMatrix p.1, p.2)) :=
    (compactMatrix_continuous.comp continuous_fst).prodMk continuous_snd
  exact Continuous.comp (f := fun p : compactIdentityComponent × Hilbert27 =>
    (compactMatrix p.1, p.2))
    (g := fun p : Matrix27 × Hilbert27 =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 27) p.1 p.2)
    Matrix.continuous_uncurry_toEuclideanCLM hc

theorem hilbert27_finrank : Module.finrank ℂ Hilbert27 = 27 := by simp [Hilbert27]

def su5RestrictionEquiv : Representation.Equiv (representation.comp SU5Coordinates.inclusion)
    SU5Coordinates.modelRepresentation :=
  .mk ((WithLp.linearEquiv 2 ℂ (Fin 27 → ℂ)).trans SU5Coordinates.actualModelEquiv) (by
    intro g
    apply LinearMap.ext
    intro v
    exact SU5Coordinates.inclusion_intertwining g (WithLp.ofLp v))

end

end GUT.E6.Minuscule
