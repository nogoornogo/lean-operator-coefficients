import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic

/-! Factored local Young actions for the supplied u²d⁴ tableaux.
Rows become alternating and columns symmetric after fermionic transfer.
The factors are small group-algebra expressions, not evaluated coordinates. -/
namespace GUT.LiSixQuarkYoungOperators
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Alternating action of the first three down slots, factored by cosets. -/
def alternatingThree (t : Fin 4 → Module.End K V) : Module.End K V :=
  (1-t 1) * (1-t 2+t 2*t 1)

def symmetricThree (u v : Module.End K V) : Module.End K V :=
  (1+u) * (1+v+v*u)

def alternatingFour (t : Fin 4 → Module.End K V) : Module.End K V :=
  alternatingThree t * (1-t 3+t 3*t 2-t 3*t 2*t 1)
def symmetricFour (t : Fin 4 → Module.End K V) : Module.End K V :=
  symmetricThree (t 1) (t 2) * (1+t 3+t 3*t 2+t 3*t 2*t 1)

/-- Down shape (3,1), with the local fermionic sign convention. -/
def shape31 (t : Fin 4 → Module.End K V) : Module.End K V :=
  alternatingThree t * (1+t 1*t 2*t 3*t 2*t 1)
/-- Down shape (2,1,1). -/
def shape211 (t : Fin 4 → Module.End K V) : Module.End K V :=
  (1-t 1) * symmetricThree (t 1*t 2*t 1) (t 3)
/-- Down shape (2,2). -/
def shape22 (t : Fin 4 → Module.End K V) : Module.End K V :=
  (1-t 1) * (1-t 3) * (1+t 1*t 2*t 1) * (1+t 2*t 3*t 2)

def down (t : Fin 4 → Module.End K V) (k : Fin 11) : Module.End K V := match k with
  | 0 | 1 | 6 => shape31 t
  | 2 | 3 | 9 => shape211 t
  | 4 | 5 => alternatingFour t
  | 7 | 8 => shape22 t
  | 10 => symmetricFour t

def primitive (k : Fin 11) : K := if k = 2 ∨ k = 9 then 1 else 2

def young (t : Fin 4 → Module.End K V) (k : Fin 11) : Module.End K V :=
  (1 / primitive (K := K) k : K) • (down t k * (if k.val < 4 then 1+t 0 else 1-t 0))

/-- Transport of the factored action uses only linearity and generator
intertwining. It does not use a character formula or finite rank calculation. -/
theorem map_young (f : V →ₗ[K] W) (t : Fin 4 → Module.End K V)
    (s : Fin 4 → Module.End K W) (h : ∀ g v, f (t g v) = s g (f v))
    (k : Fin 11) (v : V) : f (young t k v) = young s k (f v) := by
  fin_cases k <;>
    simp [young, down, primitive, shape31, shape211, shape22,
      alternatingThree, alternatingFour, symmetricThree, symmetricFour,
      Module.End.mul_apply, h]

/-- The same transport also respects an exact change of scalar field. -/
theorem map_young_semilinear {L : Type*} [Field L] {Z : Type*}
    [AddCommGroup Z] [Module L Z] {σ : K →+* L}
    (f : V →ₛₗ[σ] Z) (t : Fin 4 → Module.End K V)
    (s : Fin 4 → Module.End L Z) (h : ∀ g v, f (t g v) = s g (f v))
    (k : Fin 11) (v : V) : f (young t k v) = young s k (f v) := by
  have htwo : σ (2 : K) = (2 : L) := by
    rw [show (2 : K) = 1+1 by ring, map_add, map_one]
    ring
  fin_cases k <;>
    simp [young, down, primitive, shape31, shape211, shape22,
      alternatingThree, alternatingFour, symmetricThree, symmetricFour,
      Module.End.mul_apply, LinearMap.map_smulₛₗ, h, htwo]

end
end GUT.LiSixQuarkYoungOperators
