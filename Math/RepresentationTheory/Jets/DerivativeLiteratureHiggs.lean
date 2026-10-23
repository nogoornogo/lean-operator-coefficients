import Math.RepresentationTheory.Jets.DerivativeInterface

/-! Literal gaugeless doublet polynomials for 1008.4884v3 (5.3) and
2005.00059v6 Table 2. Formal conjugate labels are independent generators.
No physical conjugation/action or invariant-completeness theorem is presumed. -/
namespace Math.DerivativeLiteratureHiggs
set_option autoImplicit false
noncomputable section
open MvPolynomial Representation

abbrev Label := Bool × Fin 2
abbrev A := ScalarJetAlgebra.Algebra Label (Fin 4)
abbrev D := ScalarJetAlgebra.totalDerivative (S := Label) (I := Fin 4)
def h (c : Bool) (a : Fin 2) : A := X ((c,a),0)
def rho : A := h true 0*h false 0 + h true 1*h false 1
def box (p : A) : A := D 0 (D 0 p)-D 1 (D 1 p)-D 2 (D 2 p)-D 3 (D 3 p)
def pair (p q : A) : A := D 0 p*D 0 q-D 1 p*D 1 q-D 2 p*D 2 q-D 3 p*D 3 q
def kinetic : A := pair (h true 0) (h false 0)+pair (h true 1) (h false 1)
def seed (a b : ℂ) (j : Label) : A := box (h j.1 j.2)+C a*h j.1 j.2+C b*rho*h j.1 j.2
def seeds (a b : ℂ) : Set A := Set.range (seed a b)
def redundant : A := rho*kinetic
def qBox : A := rho*box rho
def leftCurrent (i : Fin 4) : A := h true 0*D i (h false 0)+h true 1*D i (h false 1)
def rightCurrent (i : Fin 4) : A := D i (h true 0)*h false 0+D i (h true 1)*h false 1
def qD : A := leftCurrent 0*rightCurrent 0-leftCurrent 1*rightCurrent 1-
  leftCurrent 2*rightCurrent 2-leftCurrent 3*rightCurrent 3

theorem box_product (p q : A) :
    box (p*q) = box p*q+p*box q+2*pair p q := by
  simp only [box, pair, ScalarJetAlgebra.totalDerivative_mul, map_add]
  ring

theorem box_rho : box rho =
    box (h true 0)*h false 0+h true 0*box (h false 0)+
    (box (h true 1)*h false 1+h true 1*box (h false 1))+2*kinetic := by
  have hadd (p q : A) : box (p+q) = box p+box q := by simp [box]; abel
  rw [rho, hadd, box_product, box_product]
  unfold kinetic
  ring

def eulerCombination (a b : ℂ) : A :=
  h true 0*seed a b (false,0)+h false 0*seed a b (true,0)+
  (h true 1*seed a b (false,1)+h false 1*seed a b (true,1))

theorem literal_reduction (a b : ℂ) :
    2*redundant-qBox-2*C a*rho^2-2*C b*rho^3 = -rho*eulerCombination a b := by
  rw [qBox, box_rho]
  dsimp [redundant, eulerCombination, seed, kinetic]
  have hr : rho = h true 0*h false 0+h true 1*h false 1 := rfl
  rw [hr]
  ring

theorem combination_mem (a b : ℂ) :
    eulerCombination a b ∈ DifferentialEquation.ideal D (seeds a b) := by
  unfold eulerCombination
  exact Ideal.add_mem _
    (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (DifferentialEquation.seed_mem D _ ⟨(false,0),rfl⟩))
      (Ideal.mul_mem_left _ _ (DifferentialEquation.seed_mem D _ ⟨(true,0),rfl⟩)))
    (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (DifferentialEquation.seed_mem D _ ⟨(false,1),rfl⟩))
      (Ideal.mul_mem_left _ _ (DifferentialEquation.seed_mem D _ ⟨(true,1),rfl⟩)))

theorem reduction_mem (a b : ℂ) :
    2*redundant-qBox-2*C a*rho^2-2*C b*rho^3 ∈
      DifferentialEquation.combined D (seeds a b) := by
  rw [literal_reduction]
  exact Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (combination_mem a b))

def input (a b : ℂ) := DerivativeInterface.equations D (seeds a b)
  (trivial ℂ Unit A) (by intro g; exact le_refl _)

theorem coefficient_relation (a b : ℂ) (f : (input a b).Coefficient) :
    2*f.val redundant-f.val qBox-2*a*f.val (rho^2)-2*b*f.val (rho^3) = 0 := by
  have hz := f.property (reduction_mem a b)
  change f.val (2*redundant-qBox-2*C a*rho^2-2*C b*rho^3) = 0 at hz
  have he : 2*redundant-qBox-2*C a*rho^2-2*C b*rho^3 =
      (2:ℂ) • redundant-qBox-(2*a) • rho^2-(2*b) • rho^3 := by
    simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    norm_num only [map_ofNat]
  rw [he, map_sub, map_sub, map_sub, map_smul, map_smul, map_smul] at hz
  simpa only [smul_eq_mul] using hz

theorem normalized_relation (a b : ℂ) (f : (input a b).Coefficient) :
    f.val redundant = (1/2:ℂ)*f.val qBox+a*f.val (rho^2)+b*f.val (rho^3) := by
  linear_combination (1/2:ℂ) * coefficient_relation a b f

def representatives : Fin 5 → A := ![redundant,qBox,rho^2,rho^3,qD]
def selectedSource : Submodule ℂ A := Submodule.span ℂ (Set.range representatives)
def selected (a b : ℂ) := (input a b).select selectedSource (by intro g; exact le_refl _)
def selectedRepresentative (i : Fin 5) : selectedSource :=
  ⟨representatives i, Submodule.subset_span ⟨i,rfl⟩⟩

theorem selected_extraction (a b : ℂ) (f : (input a b).Coefficient) (i : Fin 5) :
    (selected a b).coefficientEquiv ((input a b).restrict selectedSource
      (by intro _g; exact le_refl _) f)
        ((selected a b).projection (selectedRepresentative i)) = f.val (representatives i) := rfl

def metric (i : Fin 4) : ℂ := if i = 0 then 1 else -1
def first (c : Bool) (i : Fin 4) (a : Fin 2) : A := D i (h c a)
def m (i j : Fin 4) : A := ∑ a, first true i a*first false j a
def q1 : A := ∑ i, ∑ j, (metric i*metric j) • (m i j*m j i)
def q2 : A := ∑ i, ∑ j, (metric i*metric j) • (m i j*m i j)
def q3 : A := (∑ i, metric i • m i i)^2

/-- Raw-polynomial probes only: they do not annihilate IBP. -/
def probe (k : Fin 3) : A →ₐ[ℂ] ℂ := aeval (fun j =>
  if k = 0 then if j.1.2 = 0 ∧ j.2 = Finsupp.single 0 1 then 1 else 0
  else if k = 1 then
    if j.1.2 = 0 ∧ j.2 = Finsupp.single (if j.1.1 then 0 else 1) 1 then 1 else 0
  else if (j.1.2 = 0 ∧ j.2 = Finsupp.single 0 1) ∨
          (j.1.2 = 1 ∧ j.2 = Finsupp.single 1 1) then 1 else 0)

theorem probe_values :
    (probe 0 q1 = 1 ∧ probe 0 q2 = 1 ∧ probe 0 q3 = 1) ∧
    (probe 1 q1 = 0 ∧ probe 1 q2 = -1 ∧ probe 1 q3 = 0) ∧
    (probe 2 q1 = 2 ∧ probe 2 q2 = 2 ∧ probe 2 q3 = 0) := by
  have hs (i j : Fin 4) : (Finsupp.single i (1:ℕ) : Fin 4 →₀ ℕ) =
      Finsupp.single j 1 ↔ i = j := Finsupp.single_left_inj (by decide)
  norm_num [q1,q2,q3,m,first,h,metric,probe,Fin.sum_univ_succ,
    ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift,
    hs]

theorem raw_independent (a b c : ℂ) (hz : a • q1+b • q2+c • q3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := congrArg (probe 0) hz
  have h1 := congrArg (probe 1) hz
  have h2 := congrArg (probe 2) hz
  rcases probe_values with ⟨⟨p01,p02,p03⟩,⟨p11,p12,p13⟩,⟨p21,p22,p23⟩⟩
  simp only [map_add,map_smul,map_zero,p01,p02,p03,p11,p12,p13,p21,p22,p23,
    smul_eq_mul,mul_one,mul_zero,mul_neg_one,add_zero,zero_add] at h0 h1 h2
  constructor
  · linear_combination (1/2:ℂ)*h2+h1
  constructor
  · linear_combination -h1
  · linear_combination h0-(1/2:ℂ)*h2

theorem probe_not_ibp : probe 0
    (D 0 (h true 0*first false 0 0*first true 0 0*first false 0 0)) = 1 := by
  have hs (i j : Fin 4) : (Finsupp.single i (1:ℕ) : Fin 4 →₀ ℕ) =
      Finsupp.single j 1 ↔ i = j := Finsupp.single_left_inj (by decide)
  have h2 : (Finsupp.single (0:Fin 4) (1:ℕ)+Finsupp.single 0 1 : Fin 4 →₀ ℕ) ≠
      Finsupp.single 0 1 := by
    intro he
    have hv := congrArg (fun v : Fin 4 →₀ ℕ => v 0) he
    norm_num at hv
  norm_num [first,h,probe,ScalarJetAlgebra.totalDerivative_mul,
    ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift,hs,h2]

end
end Math.DerivativeLiteratureHiggs
