import GUT.SU6.SelectionRules.FlippedBranch.ColorNeutralSMGroup
import GUT.SU6.SelectionRules.Models.StandardSMFullGaugeMass
import GUT.SU6.Representations.ConcreteSU6Representations
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

open Math

/-!
# The full standard covering gauge group inside SU(6)

The homomorphism is (A,B,z) |-> diag(z^(-2) A, z^3 B, 1).
It is not asserted injective: the covering product has a central kernel.
The defining six-dimensional representation is identified with the heavy
space of the full-gauge mass benchmark, at the level of actual actions.
-/

set_option autoImplicit false

namespace GUT.StandardSMGroup

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor

abbrev SU6 := ActualRestriction.SU6
abbrev BlockIndex := ColorNeutralSMGroup.BlockIndex
abbrev blockIndexEquiv := ColorNeutralSMGroup.blockIndexEquiv

def colorBlock (g : GaugeGroup) : Matrix (Fin 3) (Fin 3) ℂ :=
  (↑(g.2.2 ^ (-2 : ℤ)) : ℂ) • (g.1 : Matrix (Fin 3) (Fin 3) ℂ)

def weakBlock (g : GaugeGroup) : Matrix (Fin 2) (Fin 2) ℂ :=
  (↑(g.2.2 ^ (3 : ℤ)) : ℂ) • (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)

def rawMatrix (g : GaugeGroup) : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (colorBlock g) 0 0
    (Matrix.fromBlocks (weakBlock g) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))

private theorem scale_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (z : Circle) (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    (z : ℂ) • A ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  have hz : (z : ℂ) * star (z : ℂ) = 1 := by
    simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_one,
      Complex.star_def] using
      congrArg (fun w : Circle => (w : ℂ)) (mul_inv_cancel z)
  rw [star_smul, smul_mul_smul_comm, hA, hz, one_smul]

theorem rawMatrix_unitary (g : GaugeGroup) : rawMatrix g ∈ Matrix.unitaryGroup BlockIndex ℂ := by
  have hc := scale_unitary (g.2.2 ^ (-2 : ℤ)) _
    (Matrix.specialUnitaryGroup_le_unitaryGroup g.1.prop)
  have hw := scale_unitary (g.2.2 ^ (3 : ℤ)) _
    (Matrix.specialUnitaryGroup_le_unitaryGroup g.2.1.prop)
  rw [Matrix.mem_unitaryGroup_iff] at hc hw ⊢
  simp only [Matrix.star_eq_conjTranspose] at hc hw ⊢
  change colorBlock g * (colorBlock g).conjTranspose = 1 at hc
  change weakBlock g * (weakBlock g).conjTranspose = 1 at hw
  simp only [rawMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, hc, hw, mul_one, Matrix.fromBlocks_one]

theorem rawMatrix_det (g : GaugeGroup) : Matrix.det (rawMatrix g) = 1 := by
  have hc : Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := g.1.prop.2
  have hw : Matrix.det (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := g.2.1.prop.2
  rw [rawMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp only [colorBlock, weakBlock, Matrix.det_smul, Fintype.card_fin,
    hc, hw, Matrix.det_one, mul_one]
  have h : (g.2.2 ^ (-2 : ℤ)) ^ (3 : ℕ) * (g.2.2 ^ (3 : ℤ)) ^ (2 : ℕ) = 1 := by group
  simpa only [Circle.coe_mul, Circle.coe_pow, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

def rawHom : GaugeGroup →* Matrix BlockIndex BlockIndex ℂ where
  toFun := rawMatrix
  map_one' := by simp [rawMatrix, colorBlock, weakBlock, Matrix.fromBlocks_one]
  map_mul' g h := by
    simp [rawMatrix, colorBlock, weakBlock, Matrix.fromBlocks_multiply,
      mul_pow, smul_smul, mul_comm]

def matrixHom : GaugeGroup →* Matrix (Fin 6) (Fin 6) ℂ :=
  (Matrix.reindexRingEquiv ℂ blockIndexEquiv).toMonoidHom.comp rawHom

theorem matrixHom_unitary (g : GaugeGroup) : matrixHom g ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.mp (rawMatrix_unitary g)
  change Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g) *
    star (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (rawMatrix g) *
    (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (star (rawMatrix g)) = 1
  rw [← map_mul, h, map_one]

theorem matrixHom_det (g : GaugeGroup) : Matrix.det (matrixHom g) = 1 := by
  change Matrix.det (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g)) = 1
  rw [Matrix.det_reindex_self, rawMatrix_det]

def hom : GaugeGroup →* SU6 where
  toFun g := ⟨matrixHom g, matrixHom_unitary g, matrixHom_det g⟩
  map_one' := Subtype.ext (map_one matrixHom)
  map_mul' g h := Subtype.ext (map_mul matrixHom g h)

theorem continuous_hom : Continuous hom := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : GaugeGroup =>
    Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g))
  unfold rawMatrix colorBlock weakBlock
  fun_prop (disch := simp)

def continuousHom : GaugeGroup →ₜ* SU6 where
  toMonoidHom := hom
  continuous_toFun := continuous_hom

def splitEquiv : (Fin 6 → ℂ) ≃ₗ[ℂ] StandardSMFullGaugeMass.Heavy where
  toFun v := (![v 0, v 1, v 2], (![v 3, v 4], v 5))
  invFun p := ![p.1 0, p.1 1, p.1 2, p.2.1 0, p.2.1 1, p.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
  map_add' v w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
  map_smul' r v := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl

def heavy : Representation ℂ GaugeGroup StandardSMFullGaugeMass.Heavy :=
  (twist color (-2)).prod ((twist weak 3).prod (Representation.trivial ℂ GaugeGroup ℂ))

theorem blockIndexEquiv_symm (i : Fin 6) :
    blockIndexEquiv.symm i =
      ![Sum.inl 0, Sum.inl 1, Sum.inl 2,
        Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inr 0)] i := by
  fin_cases i <;> rfl

private theorem phase_eq_coe (y : ℤ) (g : GaugeGroup) :
    phase y g = (↑(g.2.2 ^ y) : ℂ) := rfl

theorem splitEquiv_action (g : GaugeGroup) (v : Fin 6 → ℂ) :
    splitEquiv (FundamentalRepresentation.rho (hom g) v) = heavy g (splitEquiv v) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [splitEquiv, FundamentalRepresentation.rho, hom, matrixHom, rawHom,
        rawMatrix, colorBlock, weakBlock, blockIndexEquiv_symm,
        heavy, twist, color, weak, phase_eq_coe, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, mul_add, mul_assoc] <;> rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [splitEquiv, FundamentalRepresentation.rho, hom, matrixHom, rawHom,
          rawMatrix, colorBlock, weakBlock, blockIndexEquiv_symm,
          heavy, twist, color, weak, phase_eq_coe, Matrix.toLin'_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_two, mul_add, mul_assoc] <;> rfl
    · simp [splitEquiv, FundamentalRepresentation.rho, hom, matrixHom, rawHom,
        rawMatrix, colorBlock, weakBlock, blockIndexEquiv_symm,
        heavy, twist, color, weak, phase_eq_coe, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct]
      rfl

def fundamentalEquiv : Representation.Equiv
    (FundamentalRepresentation.rho.comp hom) heavy :=
  Representation.Equiv.mk splitEquiv (by
    intro g
    exact LinearMap.ext (splitEquiv_action g))

def analyticFundamentalEquiv : Representation.Equiv
    (ConcreteSU6Representations.fundamental.rho.comp hom) heavy :=
  (SplitRepresentationProjection.restrictEquiv
    ConcreteSU6Representations.fundamentalEquiv hom).trans fundamentalEquiv

def antifundamentalEquiv : Representation.Equiv
    (FundamentalRepresentation.rho.dual.comp hom) heavy.dual := by
  rw [SplitRepresentationProjection.dual_comp]
  exact SplitRepresentationProjection.dualEquiv fundamentalEquiv

def analyticAntifundamentalEquiv : Representation.Equiv
    (ConcreteSU6Representations.antifundamental.rho.comp hom) heavy.dual :=
  (SplitRepresentationProjection.restrictEquiv
    ConcreteSU6Representations.antifundamentalEquiv.symm hom).trans antifundamentalEquiv

def withResidual (H : Type*) [CommGroup H] : (GaugeGroup × H) →* SU6 :=
  hom.comp (MonoidHom.fst GaugeGroup H)

theorem heavyRho_eq (H : Type*) [CommGroup H] :
    StandardSMFullGaugeMass.heavyRho H = heavy.comp (MonoidHom.fst GaugeGroup H) := by
  apply MonoidHom.ext
  intro g
  simp [StandardSMFullGaugeMass.heavyRho, StandardSMResidualTensor.charged, heavy]

/-- The actual analytic six, with neutral residual action, is precisely
the heavy representation used in the full-gauge mass construction. -/
def neutralFundamentalEquiv (H : Type*) [CommGroup H] : Representation.Equiv
    (ConcreteSU6Representations.fundamental.rho.comp (withResidual H))
    (StandardSMFullGaugeMass.heavyRho H) := by
  rw [heavyRho_eq]
  exact SplitRepresentationProjection.restrictEquiv analyticFundamentalEquiv
    (MonoidHom.fst GaugeGroup H)

end

end GUT.StandardSMGroup
