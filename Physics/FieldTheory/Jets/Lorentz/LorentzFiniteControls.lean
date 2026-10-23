import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP

/-! Concrete full-group Lorentz transformations for finite coefficient bounds. -/
namespace Physics.LorentzFiniteControls
set_option autoImplicit false
noncomputable section
open Matrix Complex LorentzDirections Math
open scoped Matrix

def shear (z : ℂ) : Group := ⟨!![1,z;0,1],by simp [Matrix.det_fin_two]⟩

theorem shear_inverse (z : ℂ) : (shear z)⁻¹ = shear (-z) := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (!![1,-z;0,1] : Mat)*(!![1,z;0,1] : Mat) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

def flipZ : Group := ⟨!![I,0;0,-I],by simp [Matrix.det_fin_two]⟩
def flipX : Group := ⟨!![0,I;I,0],by simp [Matrix.det_fin_two]⟩
def minusZ : Group := ⟨!![-I,0;0,I],by simp [Matrix.det_fin_two]⟩
def minusX : Group := ⟨!![0,-I;-I,0],by simp [Matrix.det_fin_two]⟩

theorem flipZ_inverse : flipZ⁻¹ = minusZ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (!![-I,0;0,I] : Mat)*(!![I,0;0,-I] : Mat) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem flipX_inverse : flipX⁻¹ = minusX := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (!![0,-I;-I,0] : Mat)*(!![0,I;I,0] : Mat) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem vector_apply (g : Group) (v : Coordinates) :
    vector g v = fromPauli ((g : Mat)*pauli v*(g : Mat)ᴴ) := rfl

def signsZ : Fin 4 → ℂ := ![1,-1,-1,1]
def signsX : Fin 4 → ℂ := ![1,1,-1,-1]

theorem flipZ_direction (i : Fin 4) : direction flipZ (Finsupp.single i 1) =
    signsZ i • Finsupp.single i 1 := by
  ext j
  rw [direction_single,flipZ_inverse]
  change fromPauli ((minusZ : Mat)*pauli (Pi.single j 1)*(minusZ : Mat)ᴴ) i = _
  fin_cases i <;> fin_cases j <;>
    norm_num [signsZ,minusZ,pauli,fromPauli,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.single_apply]
  all_goals ring_nf
  all_goals simp [I_sq]

theorem flipX_direction (i : Fin 4) : direction flipX (Finsupp.single i 1) =
    signsX i • Finsupp.single i 1 := by
  ext j
  rw [direction_single,flipX_inverse]
  change fromPauli ((minusX : Mat)*pauli (Pi.single j 1)*(minusX : Mat)ᴴ) i = _
  fin_cases i <;> fin_cases j <;>
    norm_num [signsX,minusX,pauli,fromPauli,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.single_apply]
  all_goals ring_nf
  all_goals simp [I_sq]

def realRows : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3/2,-1,0,-1/2; -1,1,0,1; 0,0,1,0; 1/2,-1,0,1/2]
def imagRows : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3/2,0,1,-1/2; 0,1,0,0; 1,0,1,-1; 1/2,0,1,1/2]

theorem real_direction (i j : Fin 4) :
    (direction (shear 1) (Finsupp.single i 1)) j = realRows i j := by
  rw [direction_single,shear_inverse]
  change fromPauli ((shear (-1) : Mat)*pauli (Pi.single j 1)*(shear (-1) : Mat)ᴴ) i = _
  fin_cases i <;> fin_cases j <;>
    norm_num [realRows,shear,pauli,fromPauli,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.single_apply]
  all_goals ring_nf
  all_goals simp [I_sq]

theorem imag_direction (i j : Fin 4) :
    (direction (shear I) (Finsupp.single i 1)) j = imagRows i j := by
  rw [direction_single,shear_inverse]
  change fromPauli ((shear (-I) : Mat)*pauli (Pi.single j 1)*(shear (-I) : Mat)ᴴ) i = _
  fin_cases i <;> fin_cases j <;>
    norm_num [imagRows,shear,pauli,fromPauli,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.single_apply]
  all_goals ring_nf
  all_goals simp [I_sq]

abbrev E (i : Fin 4) : JetDirections.Direction (Fin 4) := Finsupp.single i 1

theorem real_basis (i : Fin 4) : direction (shear 1) (E i) = ∑ j, realRows i j • E j := by
  ext j
  rw [real_direction]
  simp [E,Finsupp.finsetSum_apply,Finsupp.single_apply]

theorem imag_basis (i : Fin 4) : direction (shear I) (E i) = ∑ j, imagRows i j • E j := by
  ext j
  rw [imag_direction]
  simp [E,Finsupp.finsetSum_apply,Finsupp.single_apply]

variable (b : JetDirections.Direction (Fin 4) →ₗ[ℂ] JetDirections.Direction (Fin 4) →ₗ[ℂ] ℂ)
  (h : ∀ g u v, b (direction g u) (direction g v) = b u v)

include h in
theorem offdiagonal (i j : Fin 4) (hij : i ≠ j) : b (E i) (E j) = 0 := by
  have hz := h flipZ (E i) (E j)
  have hx := h flipX (E i) (E j)
  rw [flipZ_direction,flipZ_direction] at hz
  rw [flipX_direction,flipX_direction] at hx
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at hz hx
  have zero_of_neg (c : ℂ) (hc : -c = c) : c = 0 := by
    linear_combination (-1/2 : ℂ)*hc
  simp only [E] at *
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [signsZ,signsX] at hz hx

  all_goals first | exact zero_of_neg _ hz | exact zero_of_neg _ hx

include h in
theorem diagonals :
    b (E 1) (E 1) = -b (E 0) (E 0) ∧
    b (E 2) (E 2) = -b (E 0) (E 0) ∧
    b (E 3) (E 3) = -b (E 0) (E 0) := by
  have h01 := h (shear 1) (E 0) (E 1)
  have h13 := h (shear 1) (E 1) (E 3)
  have h02 := h (shear I) (E 0) (E 2)
  simp only [real_basis,imag_basis,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    smul_eq_mul] at h01 h13 h02
  norm_num [Fin.sum_univ_succ,realRows,imagRows,offdiagonal b h,E] at h01 h13 h02
  dsimp only [E] at *
  constructor
  · linear_combination (-1/2 : ℂ)*h01+(-1/2 : ℂ)*h13
  constructor
  · linear_combination h02+(1/2 : ℂ)*h01+(-1/2 : ℂ)*h13
  · linear_combination -h01+h13

include h in
theorem trace_zero (ht : b (E 0) (E 0)-b (E 1) (E 1)-b (E 2) (E 2)-b (E 3) (E 3) = 0)
    (i j : Fin 4) : b (E i) (E j) = 0 := by
  by_cases hij : i = j
  · subst j
    obtain ⟨h1,h2,h3⟩ := diagonals b h
    have h0 : b (E 0) (E 0) = 0 := by
      rw [h1,h2,h3] at ht
      linear_combination (1/4 : ℂ)*ht
    fin_cases i <;> simp [h0,h1,h2,h3]
  · exact offdiagonal b h i j hij

end
end Physics.LorentzFiniteControls
