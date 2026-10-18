import Math.RepresentationTheory.Characters.CompactHomDimension
import Math.RepresentationTheory.InvariantCoefficientTransport

/-! Positive-root extraction and a precisely isolated, unformalized Weyl
integration input. Consumers prove implications, not the literature premise. -/
namespace Math.CompactWeylExtraction
set_option autoImplicit false
noncomputable section
open MeasureTheory Representation ContinuousRepresentationScope

variable {L : Type*} [AddCommGroup L]

def difference {R : Type*} [AddCommGroup R] (root : L) (f : L → R) : L → R :=
  fun w => f w - f (w + root)

def extractAt {R : Type*} [AddCommGroup R] : List L → (L → R) → L → R
  | [], f, w => f w
  | root :: roots, f, w => difference root (extractAt roots f) w

def constantTerm {R : Type*} [AddCommGroup R] (roots : List L) (f : L → R) : R :=
  extractAt roots f 0

/-- The alpha+beta terms cancel; no numerical multiplicity table is used. -/
theorem a2_formula {R : Type*} [AddCommGroup R] (alpha beta : L) (f : L → R) :
    constantTerm [alpha,beta,alpha+beta] f =
      f 0 - f alpha - f beta + f (alpha+alpha+beta) + f (alpha+beta+beta) -
        f (alpha+alpha+beta+beta) := by
  simp only [constantTerm,extractAt,difference,zero_add]
  have h₁ : beta + (alpha+beta) = alpha+beta+beta := by abel
  have h₂ : alpha + (alpha+beta) = alpha+alpha+beta := by abel
  have h₃ : alpha+beta+(alpha+beta) = alpha+alpha+beta+beta := by abel
  rw [h₁,h₂,h₃]
  abel

theorem intCast_extractAt (roots : List L) (f : L → ℤ) (w : L) :
    extractAt roots (fun x => (f x : ℂ)) w = ((extractAt roots f w : ℤ) : ℂ) := by
  induction roots generalizing w with
  | nil => rfl
  | cons root roots ih => simp only [extractAt,difference,ih,Int.cast_sub]

theorem intCast_constantTerm (roots : List L) (f : L → ℤ) :
    constantTerm roots (fun x => (f x : ℂ)) = ((constantTerm roots f : ℤ) : ℂ) :=
  intCast_extractAt roots f 0

variable {K T V : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [Group T]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [DecidableEq L]
  (rho : Representation ℂ K V) (torus : T →* K) (monomial : L → T → ℂ) (roots : List L)

/-- The inverse character matches coefficient-Hom counting. -/
def Presents (P : L →₀ ℤ) : Prop :=
  ∀ t, rho.character ((torus t)⁻¹) = P.sum (fun w c => (c : ℂ) * monomial w t)

/-- External theorem input. Valid applications require a compact connected
Lie group, its maximal torus, actual root/character coordinates and continuous
finite-dimensional action. None of those identifications is inferred here. -/
structure TorusReduction : Prop where
  reduce : ∀ P : L →₀ ℤ, Presents rho torus monomial P →
    (∫ g, rho.character g⁻¹ ∂TauCeti.haarProb K) = constantTerm roots (fun w => (P w : ℂ))

omit [DecidableEq L] in
theorem coefficient_dimension (hr : IsJointlyContinuous rho)
    (input : TorusReduction rho torus monomial roots) (P : L →₀ ℤ)
    (hp : Presents rho torus monomial P) :
    (Module.finrank ℂ (InvariantCoefficientTransport.Invariants rho) : ℤ) = constantTerm roots P := by
  have hi := CompactHomDimension.integral_character_mul_eq_finrank rho (Representation.trivial ℂ K ℂ)
    hr (show IsJointlyContinuous (Representation.trivial ℂ K ℂ) from continuous_snd)
  have he := input.reduce P hp
  have ht : ∀ g : K, (Representation.trivial ℂ K ℂ).character g = 1 := by
    intro g
    simp [Representation.character,Representation.trivial]
  simp only [ht,mul_one] at hi
  rw [intCast_constantTerm] at he
  have hc : ((Module.finrank ℂ (InvariantCoefficientTransport.Invariants rho) : ℤ) : ℂ) =
      ((constantTerm roots P : ℤ) : ℂ) := by exact hi.symm.trans he
  exact_mod_cast hc

end
end Math.CompactWeylExtraction
