import Physics.StandardModel.Operators.Support.Decomposition.SMCompactTorus

/-! Explicit simultaneous torus weights for the actual ten signed species. -/
namespace Physics.SMComputableSlotWeights
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor SMWeakWeightBasis SMCompactTorus
open CircleTorusCharacterLattice
open scoped TensorProduct

def colorWeight (i : Fin 3) : Weight :=
  ![if i=0 then 1 else if i=2 then -1 else 0,
    if i=1 then 1 else if i=2 then -1 else 0,0,0,0,0]
def weakWeightVector (i : Fin 2) : Weight := ![0,0,weakWeight i,0,0,0]
def hyperWeight (y : ℤ) : Weight := ![0,0,0,0,0,y]
def spinWeight (right : Bool) (i : Fin 2) : Weight :=
  ![0,0,0,if right then 0 else weakWeight i,if right then weakWeight i else 0,0]

theorem monomial_zero (t : Torus) : monomial 0 t = 1 := by
  simp [monomial,torusCharacter_apply]

theorem monomial_add (a b : Weight) (t : Torus) :
    monomial (a+b) t = monomial a t * monomial b t := by
  have h : torusCharacter (a+b) t = torusCharacter a t * torusCharacter b t := by
    simp only [torusCharacter_apply,Pi.add_apply,zpow_add]
    exact Finset.prod_mul_distrib
  exact congrArg (fun z : Circle => (z : ℂ)) h

theorem monomial_inverse (w : Weight) (t : Torus) :
    monomial w t⁻¹ = monomial (-w) t := by
  simp [monomial,torusCharacter_apply,Pi.neg_apply,Pi.inv_apply,zpow_neg]

theorem monomial_color (i : Fin 3) (t : Torus) :
    monomial (colorWeight i) t = (colorEntries t i : ℂ) := by
  fin_cases i <;> simp [monomial,torusCharacter_apply,colorWeight,colorEntries,Fin.prod_univ_succ,
    mul_inv_rev]
  exact mul_comm _ _

theorem monomial_weak (i : Fin 2) (t : Torus) :
    monomial (weakWeightVector i) t = (t 2 : ℂ) ^ weakWeight i := by
  simp [monomial,torusCharacter_apply,weakWeightVector,Fin.prod_univ_succ]

theorem monomial_hyper (y : ℤ) (t : Torus) :
    monomial (hyperWeight y) t = (t 5 : ℂ)^y := by
  simp [monomial,torusCharacter_apply,hyperWeight,Fin.prod_univ_succ]

abbrev gaugeTorus : Torus →* GaugeGroup :=
  (MonoidHom.fst GaugeGroup SMCombinedCompactAction.Spin).comp inclusion.toMonoidHom

theorem color_eigen (i : Fin 3) (t : Torus) :
    color (gaugeTorus t) (Pi.basisFun ℂ (Fin 3) i) =
      monomial (colorWeight i) t • Pi.basisFun ℂ (Fin 3) i := by
  rw [monomial_color]
  change Matrix.toLin' (colorMatrix t) (Pi.basisFun ℂ (Fin 3) i) = _
  ext j
  simp [colorMatrix,Matrix.toLin'_apply,Pi.basisFun_apply,Matrix.mulVec,Matrix.diagonal,
    Pi.single_apply,eq_comm]
  split_ifs with h
  · subst j; rfl
  · rfl

theorem weak_eigen (i : Fin 2) (t : Torus) :
    weak (gaugeTorus t) (Pi.basisFun ℂ (Fin 2) i) =
      monomial (weakWeightVector i) t • Pi.basisFun ℂ (Fin 2) i := by
  rw [monomial_weak]
  change Matrix.toLin' (TauCeti.SU2.torusHom (t 2) : Matrix (Fin 2) (Fin 2) ℂ)
    (Pi.basisFun ℂ (Fin 2) i) = _
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [weakWeight,Pi.basisFun_apply,Matrix.toLin'_apply,
      Matrix.mulVec,TauCeti.SU2.coe_torusHom,TauCeti.SU2.torusMatrix]

theorem twist_eigen {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Representation ℂ GaugeGroup V) (y : ℤ) (w : Weight) (v : V)
    (hv : ∀ t, a (gaugeTorus t) v = monomial w t • v) (t : Torus) :
    twist a y (gaugeTorus t) v = monomial (hyperWeight y + w) t • v := by
  change phase y (gaugeTorus t) • a (gaugeTorus t) v = _
  rw [hv,smul_smul,monomial_add,monomial_hyper]
  rfl

theorem tensor_eigen {V U : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (a : Representation ℂ GaugeGroup V)
    (b : Representation ℂ GaugeGroup U) (wa wb : Weight) (v : V) (u : U)
    (ha : ∀ t, a (gaugeTorus t) v = monomial wa t • v)
    (hb : ∀ t, b (gaugeTorus t) u = monomial wb t • u) (t : Torus) :
    (a.tprod b) (gaugeTorus t) (v ⊗ₜ[ℂ] u) = monomial (wa+wb) t • (v ⊗ₜ[ℂ] u) := by
  rw [Representation.tprod_apply,TensorProduct.map_tmul,ha,hb,
    TensorProduct.smul_tmul_smul,monomial_add]

theorem dual_eigen {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module ℂ V] (a : Representation ℂ GaugeGroup V)
    (b : Module.Basis I ℂ V) (w : I → Weight)
    (hb : ∀ i t, a (gaugeTorus t) (b i) = monomial (w i) t • b i) (i : I) (t : Torus) :
    a.dual (gaugeTorus t) (b.dualBasis i) = monomial (-w i) t • b.dualBasis i := by
  apply b.ext
  intro j
  change b.dualBasis i (a (gaugeTorus t)⁻¹ (b j)) =
    monomial (-w i) t * b.dualBasis i (b j)
  rw [← map_inv,hb j t⁻¹,map_smul,smul_eq_mul,Module.Basis.dualBasis_apply_self]
  by_cases hij : j=i
  · subst j; simp [monomial_inverse]
  · simp [hij]

def gaugeWeight (s : DeltaLOneSignedInput.Species) : GaugeIndex s → Weight := match s with
  | 0 => fun i => hyperWeight 1 + (colorWeight i.1 + weakWeightVector i.2)
  | 1 => fun i => hyperWeight 4 + colorWeight i
  | 2 => fun i => hyperWeight (-2) + colorWeight i
  | 3 => fun i => hyperWeight (-3) + weakWeightVector i
  | 4 => fun _ => hyperWeight (-6) + 0
  | 5 => fun i => -(hyperWeight 1 + (colorWeight i.1 + weakWeightVector i.2))
  | 6 => fun i => -(hyperWeight 4 + colorWeight i)
  | 7 => fun i => -(hyperWeight (-2) + colorWeight i)
  | 8 => fun i => -(hyperWeight (-3) + weakWeightVector i)
  | 9 => fun _ => -(hyperWeight (-6) + 0)

theorem gauge_eigen (s : DeltaLOneSignedInput.Species) (i : GaugeIndex s) (t : Torus) :
    DeltaLOneSignedFields.gauge s (gaugeTorus t) (gaugeBasis s i) =
      monomial (gaugeWeight s i) t • gaugeBasis s i := by
  have hq (i : Fin 3 × Fin 2) (t : Torus) :
      quark (gaugeTorus t) (quarkBasis i) =
        monomial (hyperWeight 1 + (colorWeight i.1 + weakWeightVector i.2)) t • quarkBasis i := by
    rcases i with ⟨i,j⟩
    apply twist_eigen
    simpa only [quarkBasis,Module.Basis.tensorProduct_apply] using
      tensor_eigen color weak _ _ _ _ (color_eigen i) (weak_eigen j)
  have hu := fun i => twist_eigen color 4 _ _ (color_eigen i)
  have hd := fun i => twist_eigen color (-2) _ _ (color_eigen i)
  have hl := fun i => twist_eigen weak (-3) _ _ (weak_eigen i)
  have he (i : Fin 1) (t : Torus) : electronRight (gaugeTorus t) (scalarBasis i) =
      monomial (hyperWeight (-6)+0) t • scalarBasis i := by
    apply twist_eigen
    intro t
    simp [monomial_zero]
  fin_cases s
  · exact hq i t
  · exact hu i t
  · exact hd i t
  · exact hl i t
  · exact he i t
  · exact dual_eigen quark quarkBasis _ hq i t
  · exact dual_eigen upRight (Pi.basisFun ℂ (Fin 3)) _ hu i t
  · exact dual_eigen downRight (Pi.basisFun ℂ (Fin 3)) _ hd i t
  · exact dual_eigen lepton (Pi.basisFun ℂ (Fin 2)) _ hl i t
  · exact dual_eigen electronRight scalarBasis _ he i t

def fieldWeight (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) : Weight :=
  gaugeWeight s i.1.1 + spinWeight (DeltaLOneSignedFields.rightHanded s) i.1.2

theorem spin_eigen (right : Bool) (i : Fin 2) (t : Torus) :
    ((WeylIndependentAction.spin right).comp SMMixedCompactWeyl.compact)
      (inclusion t).2 (Pi.basisFun ℂ (Fin 2) i) =
      monomial (spinWeight right i) t • Pi.basisFun ℂ (Fin 2) i := by
  have hm : monomial (spinWeight right i) t =
      ((if right then t 4 else t 3 : Circle) : ℂ)^weakWeight i := by
    cases right <;> simp [monomial,torusCharacter_apply,spinWeight,Fin.prod_univ_succ]
  rw [hm]
  cases right <;>
    (first
    | change Matrix.toLin' (TauCeti.SU2.torusHom (t 3) : Matrix (Fin 2) (Fin 2) ℂ)
        (Pi.basisFun ℂ (Fin 2) i) = _
    | change Matrix.toLin' (TauCeti.SU2.torusHom (t 4) : Matrix (Fin 2) (Fin 2) ℂ)
        (Pi.basisFun ℂ (Fin 2) i) = _) <;>
    fin_cases i <;> ext j <;> fin_cases j <;>
    simp [weakWeight,Pi.basisFun_apply,Matrix.toLin'_apply,Matrix.mulVec,
      TauCeti.SU2.coe_torusHom,TauCeti.SU2.torusMatrix]

theorem field_eigen (s : DeltaLOneSignedInput.Species) (i : FieldIndex s) (t : Torus) :
    SMCombinedCompactAction.field s (inclusion t) (fieldBasis s i) =
      monomial (fieldWeight s i) t • fieldBasis s i := by
  rcases i with ⟨⟨i,j⟩,k⟩
  simp only [fieldBasis,Module.Basis.tensorProduct_apply,SMCombinedCompactAction.field,
    Representation.tprod_apply,TensorProduct.map_tmul,MonoidHom.comp_apply]
  change ((DeltaLOneSignedFields.gauge s (inclusion t).1 (gaugeBasis s i)) ⊗ₜ[ℂ]
    (WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)
      (SMMixedCompactWeyl.compact (inclusion t).2) (Pi.basisFun ℂ (Fin 2) j))) ⊗ₜ[ℂ]
    Pi.basisFun ℂ (Fin 3) k = _
  rw [show DeltaLOneSignedFields.gauge s (inclusion t).1 (gaugeBasis s i) =
      monomial (gaugeWeight s i) t • gaugeBasis s i from gauge_eigen s i t]
  rw [show WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)
      (SMMixedCompactWeyl.compact (inclusion t).2) (Pi.basisFun ℂ (Fin 2) j) =
      monomial (spinWeight (DeltaLOneSignedFields.rightHanded s) j) t • Pi.basisFun ℂ (Fin 2) j
      from spin_eigen _ j t]
  simp [fieldWeight,monomial_add,TensorProduct.smul_tmul',smul_smul,mul_comm]

end
end Physics.SMComputableSlotWeights
