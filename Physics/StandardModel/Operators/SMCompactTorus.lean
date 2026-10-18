import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Math.RepresentationTheory.Characters.FiniteTorusPresentation
import Math.RepresentationTheory.Characters.CompactWeylExtraction

/-! The six-circle local SM torus and its explicit positive-root coordinates. -/
namespace GUT.SMCompactTorus
set_option autoImplicit false
noncomputable section
open Math Representation CircleTorusCharacterLattice
abbrev Torus := CircleTorusCharacterLattice.Torus (Fin 6)
abbrev Weight := Fin 6 → ℤ

def colorEntries (t : Torus) : Fin 3 → Circle := ![t 0,t 1,(t 0*t 1)⁻¹]
def colorMatrix (t : Torus) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i => (colorEntries t i : ℂ))

theorem color_mem (t : Torus) : colorMatrix t ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_,?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, colorMatrix,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    have hz : star (colorEntries t i : ℂ) = (colorEntries t i : ℂ)⁻¹ := by
      simpa using (Circle.coe_inv_eq_conj (colorEntries t i)).symm
    rw [hz]
    exact mul_inv_cancel₀ (colorEntries t i).coe_ne_zero
  · simp [colorMatrix,Matrix.det_diagonal,colorEntries,Fin.prod_univ_three,mul_assoc]

def color : Torus →* Matrix.specialUnitaryGroup (Fin 3) ℂ where
  toFun t := ⟨colorMatrix t,color_mem t⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [colorMatrix,colorEntries]
  map_mul' t u := by
    apply Subtype.ext
    change colorMatrix (t*u) = colorMatrix t * colorMatrix u
    rw [colorMatrix,colorMatrix,colorMatrix,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [colorEntries,mul_comm,mul_left_comm,mul_assoc]

theorem color_continuous : Continuous color := by
  apply continuous_induced_rng.mpr
  change Continuous colorMatrix
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_subtype_val.comp (continuous_apply 0)
  · exact continuous_subtype_val.comp (continuous_apply 1)
  · exact continuous_subtype_val.comp (((continuous_apply 0).mul (continuous_apply 1)).inv)

def inclusion : Torus →ₜ* SMCombinedCompactAction.Group where
  toMonoidHom :=
    { toFun t := ((color t,(TauCeti.SU2.torusHom (t 2),t 5)),
        (TauCeti.SU2.torusHom (t 3),TauCeti.SU2.torusHom (t 4)))
      map_one' := by simp
      map_mul' t u := by simp }
  continuous_toFun :=
    (color_continuous.prodMk ((TauCeti.SU2.continuous_torusHom.comp (continuous_apply 2)).prodMk
      (continuous_apply 5))).prodMk
      ((TauCeti.SU2.continuous_torusHom.comp (continuous_apply 3)).prodMk
        (TauCeti.SU2.continuous_torusHom.comp (continuous_apply 4)))

/-- Color: diag(z0,z1,(z0*z1)^-1); weak, left and right roots have weight 2.
Hypercharge is coordinate 5 and has no roots. -/
def alpha : Weight := ![1,-1,0,0,0,0]
def beta : Weight := ![1,2,0,0,0,0]
def weakRoot : Weight := ![0,0,2,0,0,0]
def leftRoot : Weight := ![0,0,0,2,0,0]
def rightRoot : Weight := ![0,0,0,0,2,0]
def roots : List Weight := [alpha,beta,alpha+beta,weakRoot,leftRoot,rightRoot]
def monomial (w : Weight) (t : Torus) : ℂ := (torusCharacter w t : ℂ)

end
end GUT.SMCompactTorus
