import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFlavorComponents
import Math.RepresentationTheory.Content.TripleFlavorCounting

open Math

/-! Finite interpolation of all qqql flavor components, retaining the actual
residual action as explicit equations on reconstructed functionals. -/
namespace Physics.QqqlFiniteFlavor
set_option autoImplicit false
noncomputable section
open Representation QqqlFlavorComponents
open scoped TensorProduct
variable {H Q L : Type*} [Group H] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L] {n m : ℕ}
  (q : Representation ℂ H Q) (l : Representation ℂ H L)
  (b : Module.Basis (Fin n) ℂ Q) (c : Module.Basis (Fin m) ℂ L)

abbrev Coordinates (n m : ℕ) := Fin m → TripleFlavorCoordinates.Coordinates n
abbrev Tensor := (Q ⊗[ℂ] Q) ⊗[ℂ] (Q ⊗[ℂ] L)

def tensorBasis := (b.tensorProduct b).tensorProduct (b.tensorProduct c)

def table (d : Coordinates n m) (t : Fin m) : TripleFlavorCoordinates.Space n :=
  (TripleFlavorCoordinates.equiv n).symm (d t)

def basisValue (d : Coordinates n m) (r : Fin 4) (i j k : Fin n) (t : Fin m) : ℂ :=
  ![(table d t).1.val i j k, (table d t).2.1.val i j k,
    (table d t).2.2.val j i k, (table d t).2.2.val i j k] r

def raw (d : Coordinates n m) (r : Fin 4) : Tensor (Q := Q) (L := L) →ₗ[ℂ] ℂ :=
  (tensorBasis b c).constr ℂ (fun p => basisValue d r p.1.1 p.1.2 p.2.1 p.2.2)

@[simp] theorem raw_basis (d : Coordinates n m) (r : Fin 4)
    (i j k : Fin n) (t : Fin m) :
    raw b c d r ((b i ⊗ₜ[ℂ] b j) ⊗ₜ[ℂ] (b k ⊗ₜ[ℂ] c t)) =
      basisValue d r i j k t := by
  have hb : tensorBasis b c ((i,j),(k,t)) =
      (b i ⊗ₜ[ℂ] b j) ⊗ₜ[ℂ] (b k ⊗ₜ[ℂ] c t) := by
    simp only [tensorBasis, Module.Basis.tensorProduct_apply]
  rw [← hb, raw, Module.Basis.constr_basis]

private def s01 : Tensor (Q := Q) (L := L) ≃ₗ[ℂ] Tensor (Q := Q) (L := L) :=
  FourSlotTripleAlternation.swap01
private def s12 : Tensor (Q := Q) (L := L) ≃ₗ[ℂ] Tensor (Q := Q) (L := L) :=
  FourSlotTripleAlternation.swap12

private theorem raw_relations (d : Coordinates n m) :
    (raw b c d 0).comp s01.toLinearMap = raw b c d 0 ∧
    (raw b c d 0).comp s12.toLinearMap = raw b c d 0 ∧
    (raw b c d 1).comp s01.toLinearMap = -raw b c d 1 ∧
    (raw b c d 1).comp s12.toLinearMap = -raw b c d 1 ∧
    raw b c d 2 = (raw b c d 3).comp s01.toLinearMap ∧
    (raw b c d 3).comp s12.toLinearMap = raw b c d 3 ∧
    raw b c d 3 + (raw b c d 3).comp s01.toLinearMap +
      ((raw b c d 3).comp s01.toLinearMap).comp s12.toLinearMap = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply (tensorBasis b c).ext
    rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
    simp only [tensorBasis, Module.Basis.tensorProduct_apply, LinearMap.comp_apply,
      s01, s12, FourSlotTripleAlternation.swap01, FourSlotTripleAlternation.swap12,
      LinearEquiv.coe_coe,
      TensorProduct.congr_tmul, TensorProduct.comm_tmul,
      LinearEquiv.refl_apply, TensorProduct.tensorTensorTensorComm_tmul,
      raw_basis, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.zero_apply]
    norm_num only [basisValue, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact (table d t).1.property.1 i j k
  · exact (table d t).1.property.2 i j k
  · exact (table d t).2.1.property.1 i j k
  · exact (table d t).2.1.property.2 i j k
  · rfl
  · exact (table d t).2.2.property.1 i j k
  · exact (table d t).2.2.property.2 i j k

/-- Independently checkable residual equations on finite coordinates. -/
def ResidualCondition (d : Coordinates n m) : Prop := ∀ r g,
    (raw b c d r).comp (((q.tprod q).tprod (q.tprod l)) g) =
      ((Representation.trivial ℂ H ℂ) g).comp (raw b c d r)

def reconstruct (d : Coordinates n m) (hd : ResidualCondition q l b c d) :
    QqqlFlavorComponents.residualSpace q l := by
  let f : Family q l := fun r => ⟨raw b c d r, hd r⟩
  refine ⟨f, (mem_residualSpace_iff q l f).mpr ?_⟩
  apply (condition_iff_component_relations q l f).mpr
  intro x y z h
  obtain ⟨ht01, ht12, hu01, hu12, hs, hv, hc⟩ := raw_relations b c d
  let p := (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact DFunLike.congr_fun ht01 p
  · exact DFunLike.congr_fun ht12 p
  · exact DFunLike.congr_fun hu01 p
  · exact DFunLike.congr_fun hu12 p
  · exact DFunLike.congr_fun hs p
  · exact DFunLike.congr_fun hv p
  · exact DFunLike.congr_fun hc p

def extract (f : QqqlFlavorComponents.residualSpace q l) : Coordinates n m :=
  fun t => flavorCoordinates q l b f (c t)

theorem raw_extract (f : QqqlFlavorComponents.residualSpace q l) (r : Fin 4) :
    raw b c (extract q l b c f) r = (f.val r).toLinearMap := by
  apply (tensorBasis b c).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [tensorBasis, Module.Basis.tensorProduct_apply, raw_basis]
  have hh : table (extract q l b c f) t = flavorTable q l b f (c t) :=
    (TripleFlavorCoordinates.equiv n).symm_apply_apply _
  fin_cases r <;> simp [basisValue, hh, flavorTable, mixedTable, values]
  exact ((component_relations q l f (b i) (b j) (b k) (c t)).2.2.2.2.1).symm

theorem extract_residual (f : QqqlFlavorComponents.residualSpace q l) :
    ResidualCondition q l b c (extract q l b c f) := by
  intro r g
  rw [raw_extract]
  exact (f.val r).isIntertwining' g

theorem extract_reconstruct (d : Coordinates n m) (hd : ResidualCondition q l b c d) :
    extract q l b c (reconstruct q l b c d hd) = d := by
  funext t
  change TripleFlavorCoordinates.equiv n
    (flavorTable q l b (reconstruct q l b c d hd) (c t)) = d t
  rw [← (TripleFlavorCoordinates.equiv n).apply_symm_apply (d t)]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    funext i j k
    change raw b c d 0 ((b i ⊗ₜ[ℂ] b j) ⊗ₜ[ℂ] (b k ⊗ₜ[ℂ] c t)) = _
    simp [raw_basis, basisValue, table]
  · apply Prod.ext
    · apply Subtype.ext
      funext i j k
      change raw b c d 1 ((b i ⊗ₜ[ℂ] b j) ⊗ₜ[ℂ] (b k ⊗ₜ[ℂ] c t)) = _
      simp [raw_basis, basisValue, table]
    · apply Subtype.ext
      funext i j k
      change raw b c d 3 ((b i ⊗ₜ[ℂ] b j) ⊗ₜ[ℂ] (b k ⊗ₜ[ℂ] c t)) = _
      simp [raw_basis, basisValue, table]

theorem reconstruct_extract (f : QqqlFlavorComponents.residualSpace q l) :
    reconstruct q l b c (extract q l b c f) (extract_residual q l b c f) = f := by
  apply Subtype.ext
  funext r
  apply IntertwiningMap.ext
  exact raw_extract q l b c f r

theorem raw_zero (r : Fin 4) : raw b c 0 r = 0 := by
  apply (tensorBasis b c).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [tensorBasis, Module.Basis.tensorProduct_apply, raw_basis, LinearMap.zero_apply]
  fin_cases r <;> simp [basisValue, table]

theorem raw_add (d e : Coordinates n m) (r : Fin 4) :
    raw b c (d + e) r = raw b c d r + raw b c e r := by
  apply (tensorBasis b c).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [tensorBasis, Module.Basis.tensorProduct_apply, raw_basis, LinearMap.add_apply]
  fin_cases r <;> simp [basisValue, table]

theorem raw_smul (a : ℂ) (d : Coordinates n m) (r : Fin 4) :
    raw b c (a • d) r = a • raw b c d r := by
  apply (tensorBasis b c).ext
  rintro ⟨⟨i,j⟩,⟨k,t⟩⟩
  simp only [tensorBasis, Module.Basis.tensorProduct_apply, raw_basis, LinearMap.smul_apply]
  fin_cases r <;> simp [basisValue, table]

def space : Submodule ℂ (Coordinates n m) where
  carrier := {d | ResidualCondition q l b c d}
  zero_mem' := by intro r g; rw [raw_zero]; simp
  add_mem' := by
    intro d e hd he r g
    rw [raw_add, LinearMap.add_comp, LinearMap.comp_add, hd r g, he r g]
  smul_mem' := by
    intro a d hd r g
    rw [raw_smul, LinearMap.smul_comp, LinearMap.comp_smul, hd r g]

def equiv : QqqlFlavorComponents.residualSpace q l ≃ₗ[ℂ] space q l b c where
  toFun f := ⟨extract q l b c f, extract_residual q l b c f⟩
  invFun d := reconstruct q l b c d.val d.property
  left_inv := reconstruct_extract q l b c
  right_inv d := Subtype.ext (extract_reconstruct q l b c d.val d.property)
  map_add' f g := by
    apply Subtype.ext
    funext t
    have hh : flavorTable q l b (f + g) (c t) =
        flavorTable q l b f (c t) + flavorTable q l b g (c t) := rfl
    exact (congrArg (TripleFlavorCoordinates.equiv n) hh).trans
      ((TripleFlavorCoordinates.equiv n).map_add _ _)
  map_smul' a f := by
    apply Subtype.ext
    funext t
    have hh : flavorTable q l b (a • f) (c t) = a • flavorTable q l b f (c t) := rfl
    exact (congrArg (TripleFlavorCoordinates.equiv n) hh).trans
      ((TripleFlavorCoordinates.equiv n).map_smul a _)

def exteriorEquiv : QqqlExteriorCompleteness.Sector q l ≃ₗ[ℂ] space q l b c :=
  (QqqlFlavorComponents.exteriorEquiv q l).trans (equiv q l b c)

theorem trivial_residual (d : Coordinates n m) :
    ResidualCondition (Representation.trivial ℂ H Q) (Representation.trivial ℂ H L) b c d := by
  intro r g
  ext x y z h
  simp [Representation.tprod_apply, Representation.trivial, Module.End.one_eq_id]

def trivialSpaceEquiv : Coordinates n m ≃ₗ[ℂ]
    space (Representation.trivial ℂ H Q) (Representation.trivial ℂ H L) b c where
  toFun d := ⟨d, trivial_residual b c d⟩
  invFun d := d.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- With trivial residual action every coordinate is admissible. -/
def flavorEquiv : Coordinates n m ≃ₗ[ℂ]
    QqqlExteriorCompleteness.Sector (Representation.trivial ℂ H Q)
      (Representation.trivial ℂ H L) :=
  (trivialSpaceEquiv b c).trans
    (exteriorEquiv (Representation.trivial ℂ H Q) (Representation.trivial ℂ H L) b c).symm

include b c in
theorem flavor_finrank : Module.finrank ℂ
    (QqqlExteriorCompleteness.Sector (Representation.trivial ℂ H Q)
      (Representation.trivial ℂ H L)) = m * Fintype.card (TripleFlavorCoordinates.Index n) := by
  rw [← (flavorEquiv b c).finrank_eq]
  change Module.finrank ℂ (Fin m → TripleFlavorCoordinates.Index n → ℂ) = _
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

theorem three_generation_finrank (b₃ : Module.Basis (Fin 3) ℂ Q)
    (c₃ : Module.Basis (Fin 3) ℂ L) : Module.finrank ℂ
    (QqqlExteriorCompleteness.Sector (Representation.trivial ℂ H Q)
      (Representation.trivial ℂ H L)) = 57 := by
  rw [flavor_finrank b₃ c₃, TripleFlavorCoordinates.index_card_three]

include b c in
theorem flavor_finrank_binomial : Module.finrank ℂ
    (QqqlExteriorCompleteness.Sector (Representation.trivial ℂ H Q)
      (Representation.trivial ℂ H L)) =
    m * ((n+2).choose 3 + n.choose 3 + (n*n-n + n.choose 3 * 2)) := by
  rw [flavor_finrank b c, TripleFlavorCounting.index_card]

def flatten : Coordinates n m ≃ₗ[ℂ] (Fin m × TripleFlavorCoordinates.Index n → ℂ) where
  toFun d p := d p.1 p.2
  invFun d t i := d (t,i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def flavorBasis : Module.Basis (Fin m × TripleFlavorCoordinates.Index n) ℂ
    (QqqlExteriorCompleteness.Sector (Representation.trivial ℂ H Q)
      (Representation.trivial ℂ H L)) :=
  Module.Basis.ofEquivFun ((flavorEquiv b c).symm.trans flatten)

theorem flavorBasis_independent : LinearIndependent ℂ (flavorBasis b c (H := H)) :=
  (flavorBasis b c).linearIndependent

theorem flavorBasis_spans : Submodule.span ℂ (Set.range (flavorBasis b c (H := H))) = ⊤ :=
  (flavorBasis b c).span_eq

/-- Actual field carriers use supplied equivariant identifications; no new
physical correspondence is silently inferred from the finite coordinate basis. -/
def onFieldsEquiv {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    {a : Representation ℂ (QqqlOrderedCompleteness.PhysicalGroup × H) A}
    {e : Representation ℂ (QqqlOrderedCompleteness.PhysicalGroup × H) B}
    (eq : Representation.Equiv a (ExternalInvariantTensor.external
      QqqlOrderedCompleteness.quarkSpin q))
    (el : Representation.Equiv e (ExternalInvariantTensor.external
      QqqlOrderedCompleteness.leptonSpin l)) :
    FourSlotTripleSector.sector a e ≃ₗ[ℂ] space q l b c :=
  ((QqqlExteriorCompleteness.onFieldsEquiv q l eq el).trans
    (QqqlFlavorComponents.residualEquiv q l)).trans (equiv q l b c)

end
end Physics.QqqlFiniteFlavor
