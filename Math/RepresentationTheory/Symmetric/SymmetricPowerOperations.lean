import Math.RepresentationTheory.Symmetric.SymmetricPowerDescent
import Math.RepresentationTheory.Symmetric.SymmetricMultilinearProjection
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-! Natural symmetric multiplication and splitting, with genuine group covariance. -/
namespace Math.SymmetricPowerOperations
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def concat {p q : ℕ} (v : Fin p → V) (w : Fin q → V) : Fin (p+q) → V :=
  Sum.elim v w ∘ finSumFinEquiv.symm

def blockPerm {p q : ℕ} (e : Equiv.Perm (Fin p)) (f : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (p+q)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

omit [AddCommGroup V] [Module ℂ V] in
theorem concat_perm {p q : ℕ} (e : Equiv.Perm (Fin p)) (f : Equiv.Perm (Fin q))
    (v : Fin p → V) (w : Fin q → V) :
    concat (v ∘ e) (w ∘ f) = concat v w ∘ blockPerm e f := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [concat,blockPerm]

def rawMul (p q : ℕ) : MultilinearMap ℂ (fun _ : Fin p => V)
    (MultilinearMap ℂ (fun _ : Fin q => V) (Sym[ℂ]^(p+q) V)) :=
  ((SymmetricPower.tprod ℂ).domDomCongr finSumFinEquiv.symm).currySum

@[simp] theorem rawMul_apply (p q : ℕ) (v : Fin p → V) (w : Fin q → V) :
    rawMul p q v w = SymmetricPower.tprod ℂ (concat v w) := rfl

def rightMul (p q : ℕ) : MultilinearMap ℂ (fun _ : Fin p => V)
    (SymmetricPowerDescent.symmetricMaps (A := V) (N := Sym[ℂ]^(p+q) V) q) :=
  (rawMul p q).codRestrict _ (by
    intro v e w
    change SymmetricPower.tprod ℂ (concat v (w ∘ e)) = SymmetricPower.tprod ℂ (concat v w)
    have he := concat_perm (Equiv.refl (Fin p)) e v w
    simp only [Equiv.coe_refl,Function.comp_id] at he
    rw [he]
    exact SymmetricPower.tprod_equiv _ _)

def nestedMul (p q : ℕ) : SymmetricPowerDescent.symmetricMaps (A := V)
    (N := SymmetricPowerDescent.symmetricMaps (A := V) (N := Sym[ℂ]^(p+q) V) q) p :=
  ⟨rightMul p q, by
    intro e v
    apply Subtype.ext
    ext w
    change SymmetricPower.tprod ℂ (concat (v ∘ e) w) = SymmetricPower.tprod ℂ (concat v w)
    have he := concat_perm e (Equiv.refl (Fin q)) v w
    simp only [Equiv.coe_refl,Function.comp_id] at he
    rw [he]
    exact SymmetricPower.tprod_equiv _ _⟩

def multiply (p q : ℕ) : Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V →ₗ[ℂ] Sym[ℂ]^(p+q) V :=
  TensorProduct.lift ((SymmetricPowerDescent.equiv (A := V) (N := Sym[ℂ]^(p+q) V) q).symm.toLinearMap.comp
    (SymmetricPowerDescent.lift (A := V)
      (N := SymmetricPowerDescent.symmetricMaps (A := V) (N := Sym[ℂ]^(p+q) V) q) p (nestedMul p q)))

@[simp] theorem multiply_pure (p q : ℕ) (v : Fin p → V) (w : Fin q → V) :
    multiply p q (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) =
      SymmetricPower.tprod ℂ (concat v w) := by
  change SymmetricPowerDescent.lift q
    (SymmetricPowerDescent.lift p (nestedMul p q) (SymmetricPower.tprod ℂ v))
    (SymmetricPower.tprod ℂ w) = _
  rw [SymmetricPowerDescent.lift_tprod,SymmetricPowerDescent.lift_tprod]
  rfl

def rawSplit (p q : ℕ) : MultilinearMap ℂ (fun _ : Fin (p+q) => V)
    (Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V) :=
  ((SymmetricPower.tprod ℂ).domCoprod (SymmetricPower.tprod ℂ)).domDomCongr finSumFinEquiv

def split (p q : ℕ) : Sym[ℂ]^(p+q) V →ₗ[ℂ] (Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V) :=
  SymmetricPowerDescent.lift (p+q) (SymmetricMultilinearProjection.project (p+q) (rawSplit p q))

theorem split_pure (p q : ℕ) (w : Fin (p+q) → V) :
    split p q (SymmetricPower.tprod ℂ w) = (Nat.factorial (p+q) : ℂ)⁻¹ •
      ∑ e : Equiv.Perm (Fin (p+q)),
        SymmetricPower.tprod ℂ (fun i : Fin p => w (e (finSumFinEquiv (Sum.inl i)))) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun i : Fin q => w (e (finSumFinEquiv (Sum.inr i)))) := by
  rw [split,SymmetricPowerDescent.lift_tprod]
  exact SymmetricMultilinearProjection.raw_apply _ _ _

theorem split_diagonal (p q : ℕ) (v : V) :
    split p q (SymmetricPower.tprod ℂ (fun _ => v)) =
      SymmetricPower.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin q => v) := by
  rw [split_pure]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (p+q)),one_smul]

def powerEval (p : ℕ) (φ : Module.Dual ℂ V) : Sym[ℂ]^p V →ₗ[ℂ] ℂ :=
  SymmetricPowerDescent.lift p
    ⟨(MultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compLinearMap (fun _ => φ), by
      intro e v
      change (∏ i, φ (v (e i))) = ∏ i, φ (v i)
      exact Equiv.prod_comp e (fun i => φ (v i))⟩

@[simp] theorem powerEval_pure (p : ℕ) (φ : Module.Dual ℂ V) (v : Fin p → V) :
    powerEval p φ (SymmetricPower.tprod ℂ v) = ∏ i, φ (v i) :=
  SymmetricPowerDescent.lift_tprod _ _ _

@[simp] theorem powerEval_diagonal (p : ℕ) (φ : Module.Dual ℂ V) (v : V) :
    powerEval p φ (SymmetricPower.tprod ℂ (fun _ => v)) = (φ v)^p := by
  rw [powerEval_pure]
  simp

theorem powerEval_multiply (p q : ℕ) (φ : Module.Dual ℂ V)
    (x : Sym[ℂ]^p V) (y : Sym[ℂ]^q V) :
    powerEval (p+q) φ (multiply p q (x ⊗ₜ[ℂ] y)) = powerEval p φ x * powerEval q φ y := by
  have he : (powerEval (p+q) φ).comp (multiply p q) =
      TensorProduct.lift (((LinearMap.mul ℂ ℂ).compl₂ (powerEval q φ)).comp (powerEval p φ)) := by
    apply TensorProduct.ext
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin p) V)
    rintro _ ⟨v,rfl⟩
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin q) V)
    rintro _ ⟨w,rfl⟩
    change powerEval (p+q) φ (multiply p q (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)) =
      powerEval p φ (SymmetricPower.tprod ℂ v) * powerEval q φ (SymmetricPower.tprod ℂ w)
    rw [multiply_pure,powerEval_pure,powerEval_pure,powerEval_pure]
    calc
      _ = ∏ i : Fin p ⊕ Fin q, φ (Sum.elim v w i) :=
        Fintype.prod_equiv finSumFinEquiv.symm _ _ (by intro i; rfl)
      _ = _ := by rw [Fintype.prod_sum_type]; rfl
  exact DFunLike.congr_fun he (x ⊗ₜ[ℂ] y)

def blockMultiply (p q r s : ℕ) :
    (Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V) ⊗[ℂ] (Sym[ℂ]^r V ⊗[ℂ] Sym[ℂ]^s V) →ₗ[ℂ]
      Sym[ℂ]^(p+r) V ⊗[ℂ] Sym[ℂ]^(q+s) V :=
  (TensorProduct.map (multiply p r) (multiply q s)).comp
    (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap

@[simp] theorem blockMultiply_pure (p q r s : ℕ)
    (x : Sym[ℂ]^p V) (y : Sym[ℂ]^q V) (z : Sym[ℂ]^r V) (w : Sym[ℂ]^s V) :
    blockMultiply p q r s ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) =
      multiply p r (x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] multiply q s (y ⊗ₜ[ℂ] w) := by
  simp [blockMultiply]

def biEval (p q : ℕ) (φ ψ : Module.Dual ℂ V) :
    Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V →ₗ[ℂ] ℂ :=
  TensorProduct.lift (((LinearMap.mul ℂ ℂ).compl₂ (powerEval q ψ)).comp (powerEval p φ))

@[simp] theorem biEval_pure (p q : ℕ) (φ ψ : Module.Dual ℂ V)
    (x : Sym[ℂ]^p V) (y : Sym[ℂ]^q V) :
    biEval p q φ ψ (x ⊗ₜ[ℂ] y) = powerEval p φ x * powerEval q ψ y := rfl

theorem biEval_blockMultiply (p q r s : ℕ) (φ ψ : Module.Dual ℂ V)
    (x : Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V) (y : Sym[ℂ]^r V ⊗[ℂ] Sym[ℂ]^s V) :
    biEval (p+r) (q+s) φ ψ (blockMultiply p q r s (x ⊗ₜ[ℂ] y)) =
      biEval p q φ ψ x * biEval r s φ ψ y := by
  have he : (biEval (p+r) (q+s) φ ψ).comp (blockMultiply p q r s) =
      TensorProduct.lift (((LinearMap.mul ℂ ℂ).compl₂ (biEval r s φ ψ)).comp (biEval p q φ ψ)) := by
    ext u v w z
    change biEval (p+r) (q+s) φ ψ (blockMultiply p q r s
      ((SymmetricPower.tprod ℂ u ⊗ₜ[ℂ] SymmetricPower.tprod ℂ v) ⊗ₜ[ℂ]
        (SymmetricPower.tprod ℂ w ⊗ₜ[ℂ] SymmetricPower.tprod ℂ z))) =
      biEval p q φ ψ (SymmetricPower.tprod ℂ u ⊗ₜ[ℂ] SymmetricPower.tprod ℂ v) *
        biEval r s φ ψ (SymmetricPower.tprod ℂ w ⊗ₜ[ℂ] SymmetricPower.tprod ℂ z)
    simp only [blockMultiply_pure,biEval_pure,powerEval_multiply]
    ring
  exact DFunLike.congr_fun he (x ⊗ₜ[ℂ] y)

variable {G : Type*} [Group G] (a : Representation ℂ G V)

def multiplication (p q : ℕ) : IntertwiningMap
    ((a.symmetricPower p).tprod (a.symmetricPower q)) (a.symmetricPower (p+q)) where
  toLinearMap := multiply p q
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin p) V)
    rintro _ ⟨v,rfl⟩
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin q) V)
    rintro _ ⟨w,rfl⟩
    change multiply p q (a.symmetricPower p g (SymmetricPower.tprod ℂ v) ⊗ₜ[ℂ]
      a.symmetricPower q g (SymmetricPower.tprod ℂ w)) =
      a.symmetricPower (p+q) g (multiply p q (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod,
      multiply_pure,multiply_pure,Representation.symmetricPower_apply_tprod]
    congr 1
    funext i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp [concat]

def splitting (p q : ℕ) : IntertwiningMap (a.symmetricPower (p+q))
    ((a.symmetricPower p).tprod (a.symmetricPower q)) where
  toLinearMap := split p q
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro w
    change split p q (a.symmetricPower (p+q) g (SymmetricPower.tprod ℂ w)) =
      ((a.symmetricPower p).tprod (a.symmetricPower q)) g (split p q (SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod,split_pure,split_pure,map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    simp only [Representation.tprod_apply,TensorProduct.map_tmul,
      Representation.symmetricPower_apply_tprod]

def blockShuffle (p q r s : ℕ) : Representation.Equiv
    (((a.symmetricPower p).tprod (a.symmetricPower q)).tprod
      ((a.symmetricPower r).tprod (a.symmetricPower s)))
    (((a.symmetricPower p).tprod (a.symmetricPower r)).tprod
      ((a.symmetricPower q).tprod (a.symmetricPower s))) where
  toLinearEquiv := TensorProduct.tensorTensorTensorComm ℂ _ _ _ _
  isIntertwining' g := by
    exact TensorProduct.tensorTensorTensorComm_comp_map ℂ
      ((a.symmetricPower p) g) ((a.symmetricPower q) g)
      ((a.symmetricPower r) g) ((a.symmetricPower s) g)

def blockMultiplication (p q r s : ℕ) : IntertwiningMap
    (((a.symmetricPower p).tprod (a.symmetricPower q)).tprod
      ((a.symmetricPower r).tprod (a.symmetricPower s)))
    ((a.symmetricPower (p+r)).tprod (a.symmetricPower (q+s))) :=
  ((multiplication a p r).tensor (multiplication a q s)).comp
    (blockShuffle a p q r s).toIntertwiningMap

@[simp] theorem blockMultiplication_apply (p q r s : ℕ)
    (z : (Sym[ℂ]^p V ⊗[ℂ] Sym[ℂ]^q V) ⊗[ℂ] (Sym[ℂ]^r V ⊗[ℂ] Sym[ℂ]^s V)) :
    blockMultiplication a p q r s z = blockMultiply p q r s z := rfl

end
end Math.SymmetricPowerOperations
