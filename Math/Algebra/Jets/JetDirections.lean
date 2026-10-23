import Math.Algebra.Jets.JetLinear
import Math.LinearAlgebra.Symmetric.SymmetricPolynomialPower

/-! Linear changes of ordinary derivative symbols. The monomial basis has no
factorial normalization; a direction acts by multiplication on symbols. -/
namespace Math.JetDirections
set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped TensorProduct

abbrev Direction (I : Type*) := I →₀ ℂ
abbrev Symbols (I : Type*) := MvPolynomial I ℂ

variable {S I J K : Type*}

def linearForm : Direction I →ₗ[ℂ] Symbols I := Finsupp.linearCombination ℂ X

@[simp] theorem linearForm_single (i : I) (c : ℂ) :
    linearForm (Finsupp.single i c) = c • X i := by simp [linearForm]

def symbolMap (f : Direction I →ₗ[ℂ] Direction J) : Symbols I →ₐ[ℂ] Symbols J :=
  aeval (fun i => linearForm (f (Finsupp.single i 1)))

@[simp] theorem symbolMap_X (f : Direction I →ₗ[ℂ] Direction J) (i : I) :
    symbolMap f (X i) = linearForm (f (Finsupp.single i 1)) := by simp [symbolMap]

theorem symbolMap_linearForm (f : Direction I →ₗ[ℂ] Direction J) (v : Direction I) :
    symbolMap f (linearForm v) = linearForm (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i c =>
    simp only [show Finsupp.single i c = c • Finsupp.single i (1 : ℂ) by simp,
      map_smul, linearForm_single, one_smul, symbolMap_X]

@[simp] theorem symbolMap_id :
    symbolMap (LinearMap.id : Direction I →ₗ[ℂ] Direction I) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

theorem symbolMap_comp (f : Direction I →ₗ[ℂ] Direction J)
    (g : Direction J →ₗ[ℂ] Direction K) :
    symbolMap (g.comp f) = (symbolMap g).comp (symbolMap f) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [symbolMap_linearForm]

def symbolAction {H : Type*} [Monoid H] (ρ : Representation ℂ H (Direction I)) :
    Representation ℂ H (Symbols I) where
  toFun h := (symbolMap (ρ h)).toLinearMap
  map_one' := by rw [ρ.map_one]; change (symbolMap LinearMap.id).toLinearMap = _
                 rw [symbolMap_id]; rfl
  map_mul' h k := by rw [ρ.map_mul]; exact congrArg AlgHom.toLinearMap (symbolMap_comp _ _)

def ofSymbols (s : S) : Symbols I →ₗ[ℂ] JetLinear.Jet S I :=
  (Finsupp.lmapDomain ℂ ℂ (fun α : I →₀ ℕ => (s, α))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem ofSymbols_monomial (s : S) (α : I →₀ ℕ) (c : ℂ) :
    ofSymbols s (monomial α c) = Finsupp.single (s, α) c := by
  simp [ofSymbols, MvPolynomial.monomial]

def lift (L : Symbols I →ₗ[ℂ] Symbols J) : JetLinear.Jet S I →ₗ[ℂ] JetLinear.Jet S J :=
  Finsupp.linearCombination ℂ (fun j => ofSymbols j.1 (L (monomial j.2 1)))

@[simp] theorem lift_single (L : Symbols I →ₗ[ℂ] Symbols J) (s : S) (α : I →₀ ℕ) (c : ℂ) :
    lift L (Finsupp.single (s, α) c) = c • ofSymbols s (L (monomial α 1)) := by
  simp [lift]

theorem lift_ofSymbols (L : Symbols I →ₗ[ℂ] Symbols J) (s : S) (p : Symbols I) :
    lift L (ofSymbols s p) = ofSymbols s (L p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ofSymbols_monomial, lift_single,
      show monomial α c = c • monomial α (1 : ℂ) by simp [smul_monomial],
      map_smul, map_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

@[simp] theorem lift_id :
    lift (S := S) (LinearMap.id : Symbols I →ₗ[ℂ] Symbols I) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j c
  obtain ⟨s, α⟩ := j
  simp

theorem lift_comp (L : Symbols I →ₗ[ℂ] Symbols J) (M : Symbols J →ₗ[ℂ] Symbols K) :
    lift (S := S) (M.comp L) = (lift M).comp (lift L) := by
  apply Finsupp.lhom_ext
  intro j c
  obtain ⟨s, α⟩ := j
  simp [lift_ofSymbols]

def jetMap (f : Direction I →ₗ[ℂ] Direction J) :
    JetLinear.Jet S I →ₗ[ℂ] JetLinear.Jet S J := lift (symbolMap f).toLinearMap

@[simp] theorem jetMap_id :
    jetMap (S := S) (LinearMap.id : Direction I →ₗ[ℂ] Direction I) = LinearMap.id := by
  rw [jetMap, symbolMap_id]; exact lift_id

theorem jetMap_comp (f : Direction I →ₗ[ℂ] Direction J)
    (g : Direction J →ₗ[ℂ] Direction K) :
    jetMap (S := S) (g.comp f) = (jetMap g).comp (jetMap f) := by
  rw [jetMap, symbolMap_comp]
  exact lift_comp (symbolMap f).toLinearMap (symbolMap g).toLinearMap

def jetAction {H : Type*} [Monoid H] (ρ : Representation ℂ H (Direction I)) :
    Representation ℂ H (JetLinear.Jet S I) where
  toFun h := jetMap (ρ h)
  map_one' := by rw [ρ.map_one]; exact jetMap_id
  map_mul' h k := by rw [ρ.map_mul]; exact jetMap_comp _ _

theorem shift_ofSymbols (i : I) (s : S) (p : Symbols I) :
    JetLinear.shift i (ofSymbols s p) = ofSymbols s (p * X i) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c => simp [ScalarJetAlgebra.shift, MvPolynomial.X]
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]

def shiftVector (v : Direction I) : JetLinear.Jet S I →ₗ[ℂ] JetLinear.Jet S I :=
  lift (LinearMap.mulRight ℂ (linearForm v))

theorem jetMap_shift (f : Direction I →ₗ[ℂ] Direction J) (i : I) (v : JetLinear.Jet S I) :
    jetMap f (JetLinear.shift i v) = shiftVector (f (Finsupp.single i 1)) (jetMap f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    obtain ⟨s, α⟩ := j
    rw [show Finsupp.single (s, α) c = ofSymbols s (monomial α c) by simp,
      shift_ofSymbols]
    simp only [jetMap, lift_ofSymbols, AlgHom.toLinearMap_apply, map_mul,
      symbolMap_X, shiftVector, LinearMap.mulRight_apply]

theorem shiftVector_sum [Fintype I] (v : Direction I) (x : JetLinear.Jet S I) :
    shiftVector v x = ∑ i, v i • JetLinear.shift i x := by
  have hform : linearForm v = ∑ i, v i • X i := by
    change v.sum (fun i c => c • X i) = _
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
  | single j c =>
    obtain ⟨s, α⟩ := j
    rw [show Finsupp.single (s, α) c = ofSymbols s (monomial α c) by simp]
    simp only [shiftVector, lift_ofSymbols, LinearMap.mulRight_apply, hform,
      Finset.mul_sum, mul_smul_comm, map_sum, map_smul, shift_ofSymbols]

theorem jetMap_covariant [Fintype J] (f : Direction I →ₗ[ℂ] Direction J)
    (i : I) (v : JetLinear.Jet S I) :
    jetMap f (JetLinear.shift i v) =
      ∑ j, (f (Finsupp.single i 1)) j • JetLinear.shift j (jetMap f v) := by
  rw [jetMap_shift, shiftVector_sum]

theorem linearForm_homogeneous (v : Direction I) : (linearForm v).IsHomogeneous 1 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using isHomogeneous_zero (σ := I) ℂ 1
  | add v w hv hw => simpa only [map_add] using hv.add hw
  | single i c =>
    rw [linearForm_single]
    exact (homogeneousSubmodule I ℂ 1).smul_mem c (isHomogeneous_X ℂ i)

theorem symbolMap_homogeneous (f : Direction I →ₗ[ℂ] Direction J) {d : ℕ}
    {p : Symbols I} (hp : p.IsHomogeneous d) : (symbolMap f p).IsHomogeneous d := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isHomogeneous_zero (σ := J) ℂ d
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial α c hα =>
    rw [symbolMap, aeval_monomial]
    have h := MvPolynomial.IsWeightedHomogeneous.prod α.support
      (fun i => linearForm (f (Finsupp.single i 1)) ^ α i)
      (fun i => α i • (1 : ℕ)) (fun i _ =>
        MvPolynomial.IsWeightedHomogeneous.pow
          (w := (1 : J → ℕ)) (linearForm_homogeneous (f (Finsupp.single i 1))) (α i))
    have he : (∑ i ∈ α.support, α i • (1 : ℕ)) = d := hα
    rw [he] at h
    exact h.C_mul c

theorem symbolPower_natural (f : Direction I →ₗ[ℂ] Direction J) (n : ℕ)
    (v : Fin n → Direction I) :
    symbolMap f (SymmetricPolynomialPower.equiv n (SymmetricPower.tprod ℂ v)) =
      (SymmetricPolynomialPower.equiv n (SymmetricPower.tprod ℂ (fun i => f (v i))) : Symbols J) := by
  rw [SymmetricPolynomialPower.equiv_pure, SymmetricPolynomialPower.equiv_pure, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact symbolMap_linearForm f (v i)

def jetOrder (S I : Type*) (d : ℕ) : Submodule ℂ (JetLinear.Jet S I) :=
  Finsupp.supported ℂ ℂ {j | ScalarJetAlgebra.order j.2 = d}

theorem ofSymbols_mem {d : ℕ} (s : S) {p : Symbols I} (hp : p.IsHomogeneous d) :
    ofSymbols s p ∈ jetOrder S I d := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using (jetOrder S I d).add_mem ihp ihq
  | monomial α c hα =>
    rw [ofSymbols_monomial]
    apply Finsupp.single_mem_supported
    exact hα

theorem jetMap_order (f : Direction I →ₗ[ℂ] Direction J) {d : ℕ}
    {v : JetLinear.Jet S I} (hv : v ∈ jetOrder S I d) : jetMap f v ∈ jetOrder S J d := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨s, α⟩ := j
  change lift (symbolMap f).toLinearMap (Finsupp.single (s, α) (v (s, α))) ∈ _
  rw [lift_single]
  apply Submodule.smul_mem
  apply ofSymbols_mem
  apply symbolMap_homogeneous
  exact isWeightedHomogeneous_monomial 1 α 1 (hv hj)

def shear (t : ℂ) : Direction (Fin 2) →ₗ[ℂ] Direction (Fin 2) := JetLinear.shear t

theorem shear_order_two (t : ℂ) :
    symbolMap (shear t) (X (1 : Fin 2) ^ 2) =
      X (1 : Fin 2) ^ 2 + (2 * t) • (X 0 * X 1) + t ^ 2 • X 0 ^ 2 := by
  simp only [map_pow, symbolMap_X, shear, JetLinear.shear_one, map_add,
    map_smul, linearForm_single, one_smul]
  simp only [smul_eq_C_mul]
  simp only [map_mul, map_pow, map_ofNat]
  ring

def presentation : JetLinear.Jet S I ≃ₗ[ℂ] S →₀ Symbols I :=
  (Finsupp.curryLinearEquiv ℂ).trans
    (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv ℂ).symm)

@[simp] theorem presentation_ofSymbols (s : S) (p : Symbols I) :
    presentation (ofSymbols s p) = Finsupp.single s p := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c => simp [presentation, ofSymbols, MvPolynomial.monomial]
  | add p q hp hq => simp only [map_add, hp, hq, Finsupp.single_add]

theorem ofSymbols_injective (s : S) : Function.Injective (ofSymbols (I := I) s) := by
  intro p r h
  have he := congrArg presentation h
  rw [presentation_ofSymbols, presentation_ofSymbols] at he
  exact Finsupp.single_injective s he

def orderEmbedding (s : S) (r : ℕ) : Sym[ℂ]^r (Direction I) →ₗ[ℂ] JetLinear.Jet S I :=
  (ofSymbols s).comp ((homogeneousSubmodule I ℂ r).subtype.comp
    (SymmetricPolynomialPower.equiv r).toLinearMap)

theorem orderEmbedding_injective (s : S) (r : ℕ) : Function.Injective (orderEmbedding (I := I) s r) :=
  (ofSymbols_injective s).comp
    ((Submodule.subtype_injective _).comp (SymmetricPolynomialPower.equiv r).injective)

theorem orderEmbedding_mem (s : S) (r : ℕ) (v : Sym[ℂ]^r (Direction I)) :
    orderEmbedding s r v ∈ jetOrder S I r :=
  ofSymbols_mem s (SymmetricPolynomialPower.equiv r v).property

theorem orderEmbedding_natural (f : Direction I →ₗ[ℂ] Direction I) (s : S) (r : ℕ)
    (v : Fin r → Direction I) :
    jetMap f (orderEmbedding s r (SymmetricPower.tprod ℂ v)) =
      orderEmbedding s r (SymmetricPower.tprod ℂ (fun i => f (v i))) := by
  change lift (symbolMap f).toLinearMap (ofSymbols s _) = ofSymbols s _
  rw [lift_ofSymbols]
  exact congrArg (ofSymbols s) (symbolPower_natural f r v)

end
end Math.JetDirections
