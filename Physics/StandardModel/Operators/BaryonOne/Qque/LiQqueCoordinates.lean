import Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueConvention
import TauCeti.LinearAlgebra.SymmetricPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite coordinates for the normalized printed D.38 candidate.
For arbitrary residual H, the intertwining condition remains a matrix constraint.
Only trivial residual actions admit every individual matrix-unit candidate. -/
namespace Physics.LiQqueCoordinates
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {H A B D I J K : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)
  (qBasis : Module.Basis I ℂ A) (uBasis : Module.Basis J ℂ B)
  (eBasis : Module.Basis K ℂ D)

abbrev Coordinates := Matrix (J × K) (Sym I 2) ℂ

/-- Rows are U,E flavor pairs; columns are unordered pairs of Q flavors. -/
def matrixEquiv : (Sym[ℂ]^2 A →ₗ[ℂ] B ⊗[ℂ] D) ≃ₗ[ℂ] Coordinates (I := I) (J := J) (K := K) :=
  LinearMap.toMatrix (qBasis.symmetricPower 2) (uBasis.tensorProduct eBasis)

/-- Explicit residual equivariance on the reconstructed linear map. -/
def matrixSpace : Submodule ℂ (Coordinates (I := I) (J := J) (K := K)) where
  carrier := {M | ∀ h, ((matrixEquiv qBasis uBasis eBasis).symm M).comp
    ((a.symmetricPower 2) h) = ((b.tprod d) h).comp
      ((matrixEquiv qBasis uBasis eBasis).symm M)}
  zero_mem' := by intro h; simp
  add_mem' := by
    intro M N hM hN h
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add]
    rw [hM h, hN h]
  smul_mem' := by
    intro z M hM h
    simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul]
    rw [hM h]

/-- A finite certificate has concrete entries; it retains the H constraint. -/
def homEquiv : IntertwiningMap (a.symmetricPower 2) (b.tprod d) ≃ₗ[ℂ]
    matrixSpace a b d qBasis uBasis eBasis where
  toFun f := ⟨matrixEquiv qBasis uBasis eBasis f.toLinearMap, by
    intro h
    rw [LinearEquiv.symm_apply_apply]
    exact f.isIntertwining' h⟩
  invFun M := ⟨(matrixEquiv qBasis uBasis eBasis).symm M.val, M.property⟩
  left_inv f := by
    apply IntertwiningMap.ext
    exact (matrixEquiv qBasis uBasis eBasis).symm_apply_apply f.toLinearMap
  right_inv M := by
    apply Subtype.ext
    exact (matrixEquiv qBasis uBasis eBasis).apply_symm_apply M.val
  map_add' f g := by
    apply Subtype.ext
    exact (matrixEquiv qBasis uBasis eBasis).map_add f.toLinearMap g.toLinearMap
  map_smul' z f := by
    apply Subtype.ext
    exact (matrixEquiv qBasis uBasis eBasis).map_smul z f.toLinearMap

omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ D] in
/-- The matrix constraint is exactly the usual finite intertwining equations. -/
theorem mem_matrixSpace_iff (M : Coordinates (I := I) (J := J) (K := K)) :
    M ∈ matrixSpace a b d qBasis uBasis eBasis ↔ ∀ h,
      M * LinearMap.toMatrix (qBasis.symmetricPower 2) (qBasis.symmetricPower 2)
        ((a.symmetricPower 2) h) =
      LinearMap.toMatrix (uBasis.tensorProduct eBasis) (uBasis.tensorProduct eBasis)
        ((b.tprod d) h) * M := by
  constructor
  · intro hM h
    have hh := congrArg (matrixEquiv qBasis uBasis eBasis) (hM h)
    simpa only [matrixEquiv, LinearMap.toMatrix_comp (qBasis.symmetricPower 2)
      (qBasis.symmetricPower 2) (uBasis.tensorProduct eBasis),
      LinearMap.toMatrix_comp (qBasis.symmetricPower 2)
        (uBasis.tensorProduct eBasis) (uBasis.tensorProduct eBasis),
      LinearEquiv.apply_symm_apply] using hh
  · intro hM h
    apply (matrixEquiv qBasis uBasis eBasis).injective
    simpa only [matrixEquiv, LinearMap.toMatrix_comp (qBasis.symmetricPower 2)
      (qBasis.symmetricPower 2) (uBasis.tensorProduct eBasis),
      LinearMap.toMatrix_comp (qBasis.symmetricPower 2)
        (uBasis.tensorProduct eBasis) (uBasis.tensorProduct eBasis),
      LinearEquiv.apply_symm_apply] using hM h

omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ D] [DecidableEq J] [DecidableEq K] in
/-- Evaluate Q flavor inputs without choosing an order for a symmetric pair. -/
theorem homEquiv_entry (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d))
    (i i' : I) (j : J) (k : K) :
    (homEquiv a b d qBasis uBasis eBasis f).val (j,k)
      (TauCeti.Sym.ofFn ![i,i']) =
    (uBasis.tensorProduct eBasis).repr
      (f (SymmetricPower.tprod ℂ ![qBasis i,qBasis i'])) (j,k) := by
  change LinearMap.toMatrix (qBasis.symmetricPower 2) (uBasis.tensorProduct eBasis)
    f.toLinearMap (j,k) (TauCeti.Sym.ofFn ![i,i']) = _
  rw [LinearMap.toMatrix_apply, Module.Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn]
  have hv : (fun t : Fin 2 => qBasis (![i,i'] t)) = ![qBasis i,qBasis i'] := by
    ext t
    fin_cases t <;> rfl
  rw [hv]
  rfl

/-- Coordinates are evaluations against the chosen singlet dual bases. -/
theorem residual_entry (f : IntertwiningMap (a.symmetricPower 2) (b.tprod d))
    (i i' : I) (j : J) (k : K) :
    ((QqueResidualHom.equiv a b d).symm f).val
      ((qBasis i ⊗ₜ[ℂ] qBasis i') ⊗ₜ[ℂ]
        (uBasis.dualBasis j ⊗ₜ[ℂ] eBasis.dualBasis k)) =
      (homEquiv a b d qBasis uBasis eBasis f).val (j,k)
        (TauCeti.Sym.ofFn ![i,i']) := by
  rw [QqueResidualHom.equiv_symm_tprod, homEquiv_entry]
  have h : TensorProduct.dualDistrib ℂ B D
      (uBasis.dualBasis j ⊗ₜ[ℂ] eBasis.dualBasis k) =
      (uBasis.tensorProduct eBasis).coord (j,k) := by
    apply (uBasis.tensorProduct eBasis).ext
    rintro ⟨j',k'⟩
    simp [Module.Basis.tensorProduct_apply, TensorProduct.dualDistrib_apply,
      Module.Basis.coord_apply, mul_comm]
  exact DFunLike.congr_fun h _

/-- The explicit two-sided coordinate inverse for the independently defined sector. -/
def sectorEquiv : QqueCoefficientCompleteness.Sector a b d ≃ₗ[ℂ]
    matrixSpace a b d qBasis uBasis eBasis :=
  (QqueCoefficientCompleteness.equiv a b d).symm.trans
    (homEquiv a b d qBasis uBasis eBasis)

omit [DecidableEq J] [DecidableEq K] in
theorem inverse_left (f : QqueCoefficientCompleteness.Sector a b d) :
    (sectorEquiv a b d qBasis uBasis eBasis).symm
      (sectorEquiv a b d qBasis uBasis eBasis f) = f :=
  (sectorEquiv a b d qBasis uBasis eBasis).symm_apply_apply f

omit [DecidableEq J] [DecidableEq K] in
theorem inverse_right (M : matrixSpace a b d qBasis uBasis eBasis) :
    sectorEquiv a b d qBasis uBasis eBasis
      ((sectorEquiv a b d qBasis uBasis eBasis).symm M) = M :=
  (sectorEquiv a b d qBasis uBasis eBasis).apply_symm_apply M

omit [DecidableEq J] [DecidableEq K] in
theorem sectorEquiv_symm_apply (M : matrixSpace a b d qBasis uBasis eBasis) :
    (sectorEquiv a b d qBasis uBasis eBasis).symm M =
      QqueCoefficientCompleteness.equiv a b d
        ((homEquiv a b d qBasis uBasis eBasis).symm M) := rfl

omit [DecidableEq J] [DecidableEq K] in
/-- Each invariant coordinate certificate reconstructs the literal D.38 candidate. -/
theorem inverse_is_candidate (M : matrixSpace a b d qBasis uBasis eBasis) :
    (sectorEquiv a b d qBasis uBasis eBasis).symm M =
      LiQqueConvention.candidate a b d ((QqueResidualHom.equiv a b d).symm
        ((homEquiv a b d qBasis uBasis eBasis).symm M)) := by
  exact (sectorEquiv_symm_apply a b d qBasis uBasis eBasis M).trans
    (LiQqueConvention.candidate_fromHom_eq a b d
      ((homEquiv a b d qBasis uBasis eBasis).symm M)).symm


section Trivial

/-- With trivial residual action every linear map is admissible. -/
def trivialHomEquiv : (Sym[ℂ]^2 A →ₗ[ℂ] B ⊗[ℂ] D) ≃ₗ[ℂ]
    IntertwiningMap ((Representation.trivial ℂ H A).symmetricPower 2)
      ((Representation.trivial ℂ H B).tprod (Representation.trivial ℂ H D)) where
  toFun f := ⟨f, by
    intro h
    simp [Representation.symmetricPower_apply, Representation.trivial,
      Representation.tprod_apply, Module.End.one_eq_id, SymmetricPower.map_id]⟩
  invFun f := f.toLinearMap
  left_inv f := rfl
  right_inv f := by apply IntertwiningMap.ext; rfl
  map_add' f g := by apply IntertwiningMap.ext; rfl
  map_smul' z f := by apply IntertwiningMap.ext; rfl

/-- The paper's finite-flavor pilot, before imposing an additional residual symmetry. -/
def flavorEquiv : Coordinates (I := I) (J := J) (K := K) ≃ₗ[ℂ]
    QqueCoefficientCompleteness.Sector (Representation.trivial ℂ H A)
      (Representation.trivial ℂ H B) (Representation.trivial ℂ H D) :=
  ((matrixEquiv qBasis uBasis eBasis).symm.trans (trivialHomEquiv (H := H))).trans
    (QqueCoefficientCompleteness.equiv _ _ _)

/-- Independent D.38 flavor candidates are the reconstructed matrix units. -/
def flavorBasis : Module.Basis ((J × K) × Sym I 2) ℂ
    (QqueCoefficientCompleteness.Sector (Representation.trivial ℂ H A)
      (Representation.trivial ℂ H B) (Representation.trivial ℂ H D)) :=
  (Matrix.stdBasis ℂ (J × K) (Sym I 2)).map (flavorEquiv (H := H) qBasis uBasis eBasis)

omit [DecidableEq J] [DecidableEq K] in
theorem flavor_inverse_left (M : Coordinates (I := I) (J := J) (K := K)) :
    (flavorEquiv (H := H) qBasis uBasis eBasis).symm
      (flavorEquiv (H := H) qBasis uBasis eBasis M) = M :=
  (flavorEquiv (H := H) qBasis uBasis eBasis).symm_apply_apply M

omit [DecidableEq J] [DecidableEq K] in
theorem flavor_inverse_right (f : QqueCoefficientCompleteness.Sector
    (Representation.trivial ℂ H A) (Representation.trivial ℂ H B)
    (Representation.trivial ℂ H D)) :
    flavorEquiv (H := H) qBasis uBasis eBasis
      ((flavorEquiv (H := H) qBasis uBasis eBasis).symm f) = f :=
  (flavorEquiv (H := H) qBasis uBasis eBasis).apply_symm_apply f


omit [DecidableEq J] [DecidableEq K] in
/-- Every matrix-unit basis element is the explicitly mapped paper candidate. -/
theorem flavorBasis_is_candidate (v : (J × K) × Sym I 2) :
    flavorBasis (H := H) qBasis uBasis eBasis v =
      LiQqueConvention.candidate (Representation.trivial ℂ H A)
        (Representation.trivial ℂ H B) (Representation.trivial ℂ H D)
        ((QqueResidualHom.equiv _ _ _).symm
          (trivialHomEquiv (H := H) ((matrixEquiv qBasis uBasis eBasis).symm
            (Matrix.stdBasis ℂ (J × K) (Sym I 2) v)))) := by
  rw [LiQqueConvention.candidate_fromHom_eq]
  rfl

omit [DecidableEq J] [DecidableEq K] in
theorem flavorBasis_independent :
    LinearIndependent ℂ (flavorBasis (H := H) qBasis uBasis eBasis) :=
  (flavorBasis (H := H) qBasis uBasis eBasis).linearIndependent

omit [DecidableEq J] [DecidableEq K] in
theorem flavorBasis_spans :
    Submodule.span ℂ (Set.range (flavorBasis (H := H) qBasis uBasis eBasis)) = ⊤ :=
  (flavorBasis (H := H) qBasis uBasis eBasis).span_eq

/-- The published C^[2] flavor components are exactly the finite matrix entries. -/
theorem flavor_entry (M : Coordinates (I := I) (J := J) (K := K))
    (i i' : I) (j : J) (k : K) :
    ((QqueResidualHom.equiv (Representation.trivial ℂ H A)
      (Representation.trivial ℂ H B) (Representation.trivial ℂ H D)).symm
      (trivialHomEquiv (H := H) ((matrixEquiv qBasis uBasis eBasis).symm M))).val
        ((qBasis i ⊗ₜ[ℂ] qBasis i') ⊗ₜ[ℂ]
          (uBasis.dualBasis j ⊗ₜ[ℂ] eBasis.dualBasis k)) =
        M (j,k) (TauCeti.Sym.ofFn ![i,i']) := by
  rw [residual_entry]
  change matrixEquiv qBasis uBasis eBasis
    ((matrixEquiv qBasis uBasis eBasis).symm M) _ _ = _
  rw [LinearEquiv.apply_symm_apply]

/-- Every flavor matrix has exactly the local epsilon/bracket contraction in D.38. -/
theorem flavor_paperOrdered_apply
    (M : Coordinates (I := I) (J := J) (K := K))
    (i i' : I) (j : J) (k : K)
    (c₁ c₂ c₄ : SMEpsilonTensor.Color) (w₁ w₂ : SMEpsilonTensor.Weak)
    (s₁ s₂ s₃ s₄ : WeylSpinor.Space) :
    LiQqueConvention.paperOrdered (Representation.trivial ℂ H A)
      (Representation.trivial ℂ H B) (Representation.trivial ℂ H D)
      ((QqueResidualHom.equiv _ _ _).symm
        (trivialHomEquiv (H := H) ((matrixEquiv qBasis uBasis eBasis).symm M))).val
      (((((c₁ ⊗ₜ[ℂ] w₁) ⊗ₜ[ℂ] qBasis i) ⊗ₜ[ℂ] s₁) ⊗ₜ[ℂ]
        (((c₂ ⊗ₜ[ℂ] w₂) ⊗ₜ[ℂ] qBasis i') ⊗ₜ[ℂ] s₂)) ⊗ₜ[ℂ]
        ((((1 : ℂ) ⊗ₜ[ℂ] eBasis.dualBasis k) ⊗ₜ[ℂ] s₃) ⊗ₜ[ℂ]
          ((c₄ ⊗ₜ[ℂ] uBasis.dualBasis j) ⊗ₜ[ℂ] s₄))) =
      SMEpsilonTensor.eps3 c₁ c₂ c₄ * SMEpsilonTensor.eps2 w₁ w₂ *
        M (j,k) (TauCeti.Sym.ofFn ![i,i']) *
        (SMEpsilonTensor.eps2 s₁ s₂ * SMEpsilonTensor.eps2 s₃ s₄) := by
  rw [LiQqueConvention.paperOrdered_apply, flavor_entry]
  simp only [mul_one]

omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [Group H]
  [DecidableEq J] [DecidableEq K] in
theorem flavor_index_card :
    Fintype.card ((J × K) × Sym I 2) =
      Fintype.card J * Fintype.card K * Nat.multichoose (Fintype.card I) 2 := by
  simp [Fintype.card_prod, Sym.card_sym_eq_multichoose]

end Trivial


end
end Physics.LiQqueCoordinates
