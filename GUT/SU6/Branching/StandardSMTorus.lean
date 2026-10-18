import GUT.SU6.Branching.StandardSMGroup
import GUT.SU6.Branching.PhysicalSMTorusTarget

/-!
# Compatibility of the full standard gauge action with the physical torus

The four physical circle coordinates lift into the covering gauge group.
Composing that lift with the actual SU(6) homomorphism is the existing
physical embedding at the standard cocharacter (-2,3).
-/

set_option autoImplicit false

namespace GUT.StandardSMTorus

noncomputable section

open StandardSMGaugeTensor StandardSMGroup

private def diagonalSU {n : ℕ} (z : Fin n → Circle) (hz : ∏ i, z i = 1) :
    Matrix.specialUnitaryGroup (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (z i : ℂ)), by
    constructor
    · change Matrix.diagonal (fun i => (z i : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst j
        have hi : (z i : ℂ) * star (z i : ℂ) = 1 := by
          rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
            mul_inv_cancel, Circle.coe_one]
        simpa [Matrix.one_apply] using hi
      · simp [h]
    · change Matrix.det (Matrix.diagonal (fun i => (z i : ℂ))) = 1
      rw [Matrix.det_diagonal]
      change (∏ i, Circle.coeHom (z i)) = 1
      rw [← map_prod, hz, map_one]⟩

def point (a b c z : Circle) : GaugeGroup :=
  (diagonalSU ![a, b, (a * b)⁻¹] (by simp [Fin.prod_univ_three]),
    diagonalSU ![c, c⁻¹] (by simp [Fin.prod_univ_two]), z)

def circleHom : (Fin 4 → Circle) →* GaugeGroup where
  toFun x := point (x 0) (x 1) (x 2) (x 3)
  map_one' := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [point, diagonalSU]
    · apply Prod.ext
      · apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [point, diagonalSU]
      · rfl
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]
    · apply Prod.ext
      · apply Subtype.ext
        change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp [mul_comm]
      · rfl

def toCircles : PhysicalSMTorusTarget.Group →* (Fin 4 → Circle) where
  toFun x i := AddCircle.toCircle (x.toAdd i)
  map_one' := by funext i; exact AddCircle.toCircle_zero
  map_mul' x y := by funext i; exact AddCircle.toCircle_add _ _

def hom : PhysicalSMTorusTarget.Group →* GaugeGroup := circleHom.comp toCircles

theorem matrix_point (a b c z : Circle) :
    matrixHom (point a b c z) = Matrix.diagonal
      ![(↑(z ^ (-2 : ℤ) * a) : ℂ), ↑(z ^ (-2 : ℤ) * b),
        ↑(z ^ (-2 : ℤ) * (a * b)⁻¹), ↑(z ^ (3 : ℤ) * c),
        ↑(z ^ (3 : ℤ) * c⁻¹), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixHom, rawHom, rawMatrix, colorBlock, weakBlock,
      blockIndexEquiv_symm, point, diagonalSU]

def ambientPoint (a b c z : Circle) : AmbientTorus.Torus :=
  ![z ^ (-2 : ℤ) * a, z ^ (-2 : ℤ) * b, z ^ (-2 : ℤ) * (a * b)⁻¹,
    z ^ (3 : ℤ) * c, z ^ (3 : ℤ) * c⁻¹]

theorem physical_ambientPoint (x : PhysicalSMTorusTarget.Group) :
    PhysicalSMTorusTarget.toAmbientTorus (-2) 3 x =
      ambientPoint (AddCircle.toCircle (x.toAdd 0)) (AddCircle.toCircle (x.toAdd 1))
        (AddCircle.toCircle (x.toAdd 2)) (AddCircle.toCircle (x.toAdd 3)) := by
  funext i
  change AddCircle.toCircle (PhysicalTorusCharacterBridge.ambientTorusPoint (-2) 3 x.toAdd i) = _
  fin_cases i
  · change AddCircle.toCircle (x.toAdd 0 + (-2 : ℤ) • x.toAdd 3) = _
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
    exact mul_comm _ _
  · change AddCircle.toCircle (x.toAdd 1 + (-2 : ℤ) • x.toAdd 3) = _
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
    exact mul_comm _ _
  · change AddCircle.toCircle (-x.toAdd 0 - x.toAdd 1 + (-2 : ℤ) • x.toAdd 3) = _
    rw [sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_add,
      AddCircle.toCircle_neg, AddCircle.toCircle_neg, AddCircle.toCircle_zsmul]
    change _ = AddCircle.toCircle (x.toAdd 3) ^ (-2 : ℤ) *
      (AddCircle.toCircle (x.toAdd 0) * AddCircle.toCircle (x.toAdd 1))⁻¹
    simp [mul_comm, mul_assoc]
  · change AddCircle.toCircle (x.toAdd 2 + (3 : ℤ) • x.toAdd 3) = _
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
    exact mul_comm _ _
  · change AddCircle.toCircle (-x.toAdd 2 + (3 : ℤ) • x.toAdd 3) = _
    rw [AddCircle.toCircle_add, AddCircle.toCircle_neg, AddCircle.toCircle_zsmul]
    exact mul_comm _ _

theorem coords_ambientPoint (a b c z : Circle) :
    AmbientTorus.coords (ambientPoint a b c z) =
      ![(↑(z ^ (-2 : ℤ) * a) : ℂ), ↑(z ^ (-2 : ℤ) * b),
        ↑(z ^ (-2 : ℤ) * (a * b)⁻¹), ↑(z ^ (3 : ℤ) * c),
        ↑(z ^ (3 : ℤ) * c⁻¹), 1] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have hp : ∏ j, ambientPoint a b c z j = 1 := by
      rw [Fin.prod_univ_five]
      change (z ^ (-2 : ℤ) * a) * (z ^ (-2 : ℤ) * b) *
        (z ^ (-2 : ℤ) * (a * b)⁻¹) * (z ^ (3 : ℤ) * c) * (z ^ (3 : ℤ) * c⁻¹) = 1
      simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
      group
      simp only [zpow_neg_one]
      convert mul_inv_cancel (a * b * c) using 1
      simp only [mul_inv_rev]
      ac_rfl
    change (↑((∏ j, ambientPoint a b c z j)⁻¹) : ℂ) = 1
    rw [hp, inv_one, Circle.coe_one]

theorem hom_comp : StandardSMGroup.hom.comp hom = PhysicalSMTorusTarget.embedding (-2) 3 := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change matrixHom (point (AddCircle.toCircle (x.toAdd 0))
    (AddCircle.toCircle (x.toAdd 1)) (AddCircle.toCircle (x.toAdd 2))
    (AddCircle.toCircle (x.toAdd 3))) = Matrix.diagonal
      (AmbientTorus.coords (PhysicalSMTorusTarget.toAmbientTorus (-2) 3 x))
  rw [matrix_point, physical_ambientPoint, coords_ambientPoint]

theorem continuous_hom : Continuous hom := by
  change Continuous (fun x : PhysicalSMTorusTarget.Group =>
    point (AddCircle.toCircle (x.toAdd 0)) (AddCircle.toCircle (x.toAdd 1))
      (AddCircle.toCircle (x.toAdd 2)) (AddCircle.toCircle (x.toAdd 3)))
  unfold point diagonalSU
  fun_prop (disch := simp)

theorem restrict_eq {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (rho : Representation ℂ ActualRestriction.SU6 V) :
    (rho.comp StandardSMGroup.hom).comp hom = rho.comp (PhysicalSMTorusTarget.embedding (-2) 3) := by
  change rho.comp (StandardSMGroup.hom.comp hom) = _
  rw [hom_comp]

theorem withResidual_comp (H : Type*) [CommGroup H] :
    (StandardSMGroup.withResidual H).comp (hom.prodMap (MonoidHom.id H)) =
      (PhysicalSMTorusTarget.embedding (-2) 3).comp
        (MonoidHom.fst PhysicalSMTorusTarget.Group H) := by
  apply MonoidHom.ext
  intro g
  exact DFunLike.congr_fun hom_comp g.1

/-- The covering product must not be mistaken for an injectively embedded
subgroup: a nonidentity central element maps to the identity. -/
theorem covering_not_injective : ¬Function.Injective StandardSMGroup.hom := by
  intro hinj
  have he : StandardSMGroup.hom (point 1 1 (-1) (-1)) = StandardSMGroup.hom 1 := by
    apply Subtype.ext
    change matrixHom (point 1 1 (-1) (-1)) = matrixHom 1
    rw [matrix_point, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  have hz : (-1 : Circle) = 1 := congrArg (fun g : GaugeGroup => g.2.2) (hinj he)
  have hc := congrArg (fun z : Circle => (z : ℂ)) hz
  norm_num at hc

end

end GUT.StandardSMTorus
