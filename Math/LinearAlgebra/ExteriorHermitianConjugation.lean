import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic

/-! Complex-conjugating anti-involution on an exterior algebra from an
involutive semilinear field conjugation. No Clifford scalar-fixed star used. -/
namespace Math.ExteriorHermitianConjugation
set_option autoImplicit false
noncomputable section

/-- Separate target type with conjugate scalar action. -/
def Twisted (A : Type*) := A
variable {A : Type*} [Ring A] [Algebra ℂ A]
instance : Ring (Twisted A) := inferInstanceAs (Ring A)
instance : Algebra ℂ (Twisted A) where
  smul z x := star z • (show A from x)
  algebraMap := (algebraMap ℂ A).comp (starRingEnd ℂ)
  commutes' z x := Algebra.commutes (star z) (show A from x)
  smul_def' z x := Algebra.smul_def (star z) (show A from x)

def untwist : Twisted A ≃+* A := RingEquiv.refl A

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
abbrev EA := ExteriorAlgebra ℂ V

def twistedGenerator (c : V →ₛₗ[starRingEnd ℂ] V) : V →ₗ[ℂ] Twisted (EA (V := V)) where
  toFun v := ExteriorAlgebra.ι ℂ (c v)
  map_add' x y := by simp [map_add]; rfl
  map_smul' z v := by
    change ExteriorAlgebra.ι ℂ (c (z • v)) =
      algebraMap ℂ (EA (V := V)) (star z) * ExteriorAlgebra.ι ℂ (c v)
    rw [c.map_smulₛₗ, map_smul]
    rfl

def conjugate (c : V →ₛₗ[starRingEnd ℂ] V) : EA (V := V) →+* EA (V := V) :=
  untwist.toRingHom.comp (ExteriorAlgebra.lift ℂ
    ⟨twistedGenerator c, fun v => ExteriorAlgebra.ι_sq_zero (c v)⟩).toRingHom

@[simp] theorem conjugate_generator (c : V →ₛₗ[starRingEnd ℂ] V) (v : V) :
    conjugate c (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (c v) := by
  exact congrArg untwist (ExteriorAlgebra.lift_ι_apply ℂ (twistedGenerator c) _ v)

@[simp] theorem conjugate_scalar (c : V →ₛₗ[starRingEnd ℂ] V) (z : ℂ) :
    conjugate c (algebraMap ℂ (EA (V := V)) z) = algebraMap ℂ _ (star z) := by
  exact congrArg untwist ((ExteriorAlgebra.lift ℂ
    ⟨twistedGenerator c, fun v => ExteriorAlgebra.ι_sq_zero (c v)⟩).commutes z)

theorem conjugate_smul (c : V →ₛₗ[starRingEnd ℂ] V) (z : ℂ) (x : EA (V := V)) :
    conjugate c (z • x) = star z • conjugate c x := by
  rw [Algebra.smul_def, map_mul, conjugate_scalar, Algebra.smul_def]

theorem conjugate_involutive (c : V →ₛₗ[starRingEnd ℂ] V)
    (hc : ∀ v, c (c v) = v) (x : EA (V := V)) : conjugate c (conjugate c x) = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp
  | ι v => simp [hc]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

def adjoint (c : V →ₛₗ[starRingEnd ℂ] V) (x : EA (V := V)) : EA (V := V) :=
  CliffordAlgebra.reverse (conjugate c x)

theorem adjoint_mul (c : V →ₛₗ[starRingEnd ℂ] V) (x y : EA (V := V)) :
    adjoint c (x*y) = adjoint c y * adjoint c x := by
  simp only [adjoint, map_mul, CliffordAlgebra.reverse.map_mul]

theorem adjoint_smul (c : V →ₛₗ[starRingEnd ℂ] V) (z : ℂ) (x : EA (V := V)) :
    adjoint c (z • x) = star z • adjoint c x := by
  simp [adjoint, conjugate_smul]

theorem conjugate_reverse (c : V →ₛₗ[starRingEnd ℂ] V) (x : EA (V := V)) :
    conjugate c (CliffordAlgebra.reverse x) = CliffordAlgebra.reverse (conjugate c x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp
  | ι v => simp
  | mul x y hx hy => simp only [CliffordAlgebra.reverse.map_mul, map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem adjoint_involutive (c : V →ₛₗ[starRingEnd ℂ] V)
    (hc : ∀ v, c (c v) = v) (x : EA (V := V)) : adjoint c (adjoint c x) = x := by
  simp [adjoint, conjugate_reverse, conjugate_involutive c hc]


/-- Pointwise conjugation combined with a supplied involutive index swap. -/
def coordinateConjugation {I : Type*} (σ : I → I) :
    (I → ℂ) →ₛₗ[starRingEnd ℂ] (I → ℂ) where
  toFun v i := star (v (σ i))
  map_add' v w := by ext i; simp
  map_smul' z v := by ext i; simp

theorem coordinateConjugation_involutive {I : Type*} (σ : I → I)
    (hσ : ∀ i, σ (σ i) = i) (v : I → ℂ) :
    coordinateConjugation σ (coordinateConjugation σ v) = v := by
  ext i
  simp [coordinateConjugation, hσ]

theorem coordinateConjugation_basis {I : Type*} [Fintype I] [DecidableEq I]
    (σ : I → I) (hσ : ∀ i, σ (σ i) = i) (i : I) :
    coordinateConjugation σ (Pi.basisFun ℂ I i) = Pi.basisFun ℂ I (σ i) := by
  ext j
  have h : (σ j = i) ↔ (j = σ i) := ⟨fun h => by rw [← h, hσ], fun h => by rw [h, hσ]⟩
  simp [coordinateConjugation, Pi.basisFun_apply, Pi.single_apply, h]

/-- Local star structure; keeping it as data avoids replacing mathlib's
scalar-fixed Clifford star globally. -/
abbrev starRing (c : V →ₛₗ[starRingEnd ℂ] V) (hc : ∀ v, c (c v) = v) :
    StarRing (EA (V := V)) where
  star := adjoint c
  star_involutive := adjoint_involutive c hc
  star_mul := adjoint_mul c
  star_add x y := by simp [adjoint]

abbrev starModule (c : V →ₛₗ[starRingEnd ℂ] V) (hc : ∀ v, c (c v) = v) :
    @StarModule ℂ (EA (V := V)) inferInstance (starRing c hc).toStar inferInstance := by
  let : StarRing (EA (V := V)) := starRing c hc
  exact ⟨adjoint_smul c⟩

end
end Math.ExteriorHermitianConjugation
