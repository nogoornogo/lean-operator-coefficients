import Physics.StandardModel.Operators.Dipole.DipoleCouplingModel
import Math.LinearAlgebra.Selection.PolynomialSelectedPaths

open Math

/-! Certified model registration. Matching is a model-author obligation;
all residual conclusions are restricted to the registered admissible domain. -/
namespace Physics.DipoleModelInterface
set_option autoImplicit false
noncomputable section
open Representation

variable {H A B X : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [FiniteDimensional ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

structure Registered where
  admissible : Set X
  mu : A
  electron : Module.Dual ℂ B
  coefficients : X → DipoleFlavorSelection.Coefficients a b
  residual : X → (IntertwiningMap a b × IntertwiningMap a b)
  correspondence : ∀ x ∈ admissible, (DipoleSMCoefficient.equiv a b) (coefficients x) = residual x

namespace Registered
variable {a b} (r : Registered (X := X) a b)

def observe (x : X) : ℂ × ℂ :=
  DipoleFlavorSelection.selector a b r.mu r.electron (r.coefficients x)

def NonzeroInput (x : X) : Prop := x ∈ r.admissible ∧ r.observe x ≠ 0

theorem selected (x : X) (hx : x ∈ r.admissible) : r.observe x =
    (r.electron ((r.residual x).1 r.mu), r.electron ((r.residual x).2 r.mu)) := by
  change DipoleFlavorSelection.residualSelector a b r.mu r.electron
    ((DipoleSMCoefficient.equiv a b) (r.coefficients x)) = _
  rw [r.correspondence x hx]
  rfl

theorem nonzero_iff (x : X) : r.NonzeroInput x ↔ x ∈ r.admissible ∧
    (r.electron ((r.residual x).1 r.mu) ≠ 0 ∨
      r.electron ((r.residual x).2 r.mu) ≠ 0) := by
  unfold NonzeroInput
  by_cases hx : x ∈ r.admissible
  · rw [r.selected x hx]
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or]
  · simp [hx]

theorem nonzero_of_channel (x : X) (hx : x ∈ r.admissible)
    (h : r.electron ((r.residual x).1 r.mu) ≠ 0 ∨
      r.electron ((r.residual x).2 r.mu) ≠ 0) : r.NonzeroInput x :=
  (r.nonzero_iff x).mpr ⟨hx,h⟩

theorem forbidden_of_distinct_weights (g : H) (alpha beta : ℂ)
    (hmu : a g r.mu = alpha • r.mu)
    (he : ∀ y : B, r.electron (b g y) = beta * r.electron y)
    (hne : alpha ≠ beta) : ∀ x, ¬ r.NonzeroInput x := by
  intro x hx
  exact hx.2 (DipoleFlavorSelection.forbidden_of_distinct_weights a b r.mu r.electron
    g alpha beta hmu he hne (r.coefficients x))

def restrict (s : Set X) : Registered (X := X) a b :=
  { r with admissible := r.admissible ∩ s
           correspondence := fun x hx => r.correspondence x hx.1 }

theorem nonzero_restrict_iff (s : Set X) (x : X) :
    (r.restrict s).NonzeroInput x ↔ r.NonzeroInput x ∧ x ∈ s := by
  change (x ∈ r.admissible ∧ x ∈ s) ∧ r.observe x ≠ 0 ↔ _
  unfold NonzeroInput
  tauto

def pullback {Y : Type*} (f : Y → X) : Registered (X := Y) a b where
  admissible := f ⁻¹' r.admissible
  mu := r.mu
  electron := r.electron
  coefficients y := r.coefficients (f y)
  residual y := r.residual (f y)
  correspondence y hy := r.correspondence (f y) hy

@[simp] theorem observe_pullback {Y : Type*} (f : Y → X) (y : Y) :
    (r.pullback f).observe y = r.observe (f y) := rfl

@[simp] theorem nonzero_pullback_iff {Y : Type*} (f : Y → X) (y : Y) :
    (r.pullback f).NonzeroInput y ↔ r.NonzeroInput (f y) := Iff.rfl

theorem exists_pullback_iff {Y : Type*} (f : Y → X) :
    (∃ y, (r.pullback f).NonzeroInput y) ↔
    ∃ x ∈ Set.range f, r.NonzeroInput x := by
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨f y, ⟨y,rfl⟩,hy⟩
  · rintro ⟨x,⟨y,rfl⟩,hy⟩
    exact ⟨y,hy⟩

def withCoefficients (F : X → DipoleFlavorSelection.Coefficients a b)
    (hF : ∀ x ∈ r.admissible, (DipoleSMCoefficient.equiv a b) (F x) = r.residual x) :
    Registered (X := X) a b :=
  { r with coefficients := F, correspondence := hF }

theorem nonzero_withCoefficients_iff (F : X → DipoleFlavorSelection.Coefficients a b)
    (hF : ∀ x ∈ r.admissible, (DipoleSMCoefficient.equiv a b) (F x) = r.residual x)
    (x : X) : (r.withCoefficients F hF).NonzeroInput x ↔ r.NonzeroInput x :=
  ((r.withCoefficients F hF).nonzero_iff x).trans (r.nonzero_iff x).symm

end Registered

def ofResidual (domain : Set X) (mu : A) (electron : Module.Dual ℂ B)
    (k : X → (IntertwiningMap a b × IntertwiningMap a b)) : Registered (X := X) a b where
  admissible := domain
  mu := mu
  electron := electron
  coefficients x := (DipoleSMCoefficient.equiv a b).symm (k x)
  residual := k
  correspondence _ _ := LinearEquiv.apply_symm_apply _ _

def ofCouplings {M U V : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (m : Representation ℂ H M) (model : DipoleCouplingModel.Couplings (X := U) (Y := V) a b m)
    (domain : Set X) (u : X → U) (v : X → V) (mu : A) (electron : Module.Dual ℂ B) :
    Registered (X := X) a b :=
  ofResidual a b domain mu electron (fun x => DipoleCouplingModel.residual a b m model (u x) (v x))

variable {S I : Type*} [Fintype I]

/-- An expansion certificate on the actual coordinate product. Its equality
is not claimed to prove a model's physical matching calculation. -/
structure PolynomialCertificate (r : Registered (X := S → ℂ) a b) where
  coordinates : S → Set ℂ
  infinite : ∀ j, (coordinates j).Infinite
  domain_eq : r.admissible = Set.pi Set.univ coordinates
  paths : I → (IntertwiningMap a b × IntertwiningMap a b)
  weights : I → MvPolynomial S ℂ
  expansion : ∀ x ∈ r.admissible, r.residual x =
    WeightedSelectedPaths.synthesis paths (fun y i => MvPolynomial.eval y (weights i)) x

namespace PolynomialCertificate
variable {a b} {r : Registered (X := S → ℂ) a b}
  (c : PolynomialCertificate (I := I) a b r)

def grouped (d : S →₀ ℕ) : ℂ × ℂ :=
  (∑ i, r.electron ((c.paths i).1 r.mu) * (c.weights i).coeff d,
   ∑ i, r.electron ((c.paths i).2 r.mu) * (c.weights i).coeff d)

/-- Preserve an expansion certificate when attaching a model author's full
coefficient calculation. The correspondence obligation is still explicit. -/
def withCoefficients (F : (S → ℂ) → DipoleFlavorSelection.Coefficients a b)
    (hF : ∀ x ∈ r.admissible, (DipoleSMCoefficient.equiv a b) (F x) = r.residual x) :
    PolynomialCertificate (I := I) a b (r.withCoefficients F hF) where
  coordinates := c.coordinates
  infinite := c.infinite
  domain_eq := c.domain_eq
  paths := c.paths
  weights := c.weights
  expansion := c.expansion

theorem exists_nonzero_iff : (∃ x, r.NonzeroInput x) ↔ ∃ d, c.grouped d ≠ 0 := by
  have h := PolynomialSelectedPaths.pair_exists_nonzero_on_box_iff_coefficient
    c.paths c.weights (DipoleFlavorSelection.residualSelector a b r.mu r.electron)
    c.coordinates c.infinite
  have he : (∃ x, r.NonzeroInput x) ↔ ∃ x ∈ Set.pi Set.univ c.coordinates,
      DipoleFlavorSelection.residualSelector a b r.mu r.electron
        (WeightedSelectedPaths.synthesis c.paths (fun y i => MvPolynomial.eval y (c.weights i)) x) ≠ 0 := by
    constructor <;> rintro ⟨x,hx,hn⟩
    · refine ⟨x, by simpa only [← c.domain_eq] using hx, ?_⟩
      have hs := r.selected x hx
      rw [c.expansion x hx] at hs
      exact fun hz => hn (hs.trans hz)
    · have hd : x ∈ r.admissible := by simpa only [c.domain_eq] using hx
      refine ⟨x,hd,?_⟩
      rw [r.selected x hd, c.expansion x hd]
      exact hn
  rw [he]
  simpa only [grouped, DipoleFlavorSelection.residualSelector, DipoleFlavorSelection.evaluation,
    LinearMap.coe_mk, AddHom.coe_mk, ne_eq, Prod.ext_iff,
    Prod.fst_zero, Prod.snd_zero, not_and_or] using h

theorem no_nonzero_iff : (∀ x, ¬ r.NonzeroInput x) ↔ ∀ d, c.grouped d = 0 := by
  have h := not_congr c.exists_nonzero_iff
  simpa only [not_exists, not_not] using h

end PolynomialCertificate
end
end Physics.DipoleModelInterface
