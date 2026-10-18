import GUT.PatiSalam.Embeddings.StandardModel
import GUT.PatiSalam.Matching.ComponentAdmission

/-! Genuine PS tensor representations and their SM component inclusions. -/
namespace GUT.PatiSalam.ComponentRepresentations
set_option autoImplicit false
noncomputable section
open StandardSMGaugeTensor StandardModelEmbedding
open scoped TensorProduct
abbrev Four := Fin 4 → ℂ
abbrev Two := Fin 2 → ℂ
abbrev Multiplet := Four ⊗[ℂ] Two

def four : Representation ℂ PSGroup Four where
  toFun g := Matrix.toLin' (g.1 : Matrix (Fin 4) (Fin 4) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _
def left : Representation ℂ PSGroup Two where
  toFun g := Matrix.toLin' (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _
def right : Representation ℂ PSGroup Two where
  toFun g := Matrix.toLin' (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _
def fL : Representation ℂ PSGroup Multiplet := four.tprod left
def fR : Representation ℂ PSGroup Multiplet := four.tprod right

def colorIn : SMEpsilonTensor.Color →ₗ[ℂ] Four where
  toFun v a := Sum.elim v (fun _ => 0) (indexEquiv.symm a)
  map_add' v w := by ext a; cases h : indexEquiv.symm a <;> simp [h]
  map_smul' c v := by ext a; cases h : indexEquiv.symm a <;> simp [h]

def leptonIn : ℂ →ₗ[ℂ] Four where
  toFun s a := Sum.elim (fun _ => 0) (fun _ => s) (indexEquiv.symm a)
  map_add' v w := by ext a; cases h : indexEquiv.symm a <;> simp [h]
  map_smul' c v := by ext a; cases h : indexEquiv.symm a <;> simp [h]

@[simp] theorem colorIn_color (v : SMEpsilonTensor.Color) (a : Fin 3) :
    colorIn v (indexEquiv (Sum.inl a)) = v a := by simp [colorIn]
@[simp] theorem colorIn_lepton (v : SMEpsilonTensor.Color) (a : Fin 1) :
    colorIn v (indexEquiv (Sum.inr a)) = 0 := by simp [colorIn]
@[simp] theorem leptonIn_color (s : ℂ) (a : Fin 3) :
    leptonIn s (indexEquiv (Sum.inl a)) = 0 := by simp [leptonIn]
@[simp] theorem leptonIn_lepton (s : ℂ) (a : Fin 1) :
    leptonIn s (indexEquiv (Sum.inr a)) = s := by simp [leptonIn]

theorem four_apply_index (g : GaugeGroup) (v : Four) (a : Index) :
    four (hom g) v (indexEquiv a) =
      ∑ b : Index, rawMatrix g a b * v (indexEquiv b) := by
  change ∑ b : Fin 4, matrixHom g (indexEquiv a) b * v b = _
  rw [← Fintype.sum_equiv indexEquiv]
  intro b
  simp [matrixHom,Matrix.reindex_apply,rawHom]

theorem colorIn_equivariant (g : GaugeGroup) (v : SMEpsilonTensor.Color) :
    four (hom g) (colorIn v) = colorIn (twist color 1 g v) := by
  ext a
  obtain ⟨a,rfl⟩ := indexEquiv.surjective a
  rw [four_apply_index]
  cases a with
  | inl a =>
      simp [rawMatrix,colorBlock,leptonBlock,Fintype.sum_sum_type,
      colorIn,twist,color,phase,Matrix.toLin'_apply,Matrix.mulVec, dotProduct,
      Finset.mul_sum,mul_assoc,Circle.coeHom]
      rfl
  | inr a => simp [rawMatrix,Fintype.sum_sum_type,colorIn]

theorem leptonIn_equivariant (g : GaugeGroup) (s : ℂ) :
    four (hom g) (leptonIn s) = leptonIn (phase (-3) g * s) := by
  ext a
  obtain ⟨a,rfl⟩ := indexEquiv.surjective a
  rw [four_apply_index]
  cases a with
  | inl a => simp [rawMatrix,Fintype.sum_sum_type,leptonIn]
  | inr a =>
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      simp [rawMatrix,leptonBlock,Fintype.sum_sum_type,leptonIn,phase,Circle.coeHom]
      exact Or.inl rfl

def arrayEquiv : Multiplet ≃ₗ[ℂ] ComponentAdmission.Array :=
  (TensorProduct.piLeft ℂ Two (fun _ : Fin 4 => ℂ)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.lid ℂ Two)

@[simp] theorem array_tmul (v : Four) (w : Two) (a : Fin 4) (i : Fin 2) :
    arrayEquiv (v ⊗ₜ[ℂ] w) a i = v a * w i := by
  simp [arrayEquiv,TensorProduct.piLeft,TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

def qIn : Quark →ₗ[ℂ] Multiplet := TensorProduct.map colorIn LinearMap.id
def lIn : Two →ₗ[ℂ] Multiplet :=
  (TensorProduct.map leptonIn LinearMap.id).comp (TensorProduct.lid ℂ Two).symm.toLinearMap

def rightIn (i : Fin 2) : Four →ₗ[ℂ] Multiplet :=
  TensorProduct.mk ℂ Four Two |>.flip (Pi.single i 1)
def uIn : SMEpsilonTensor.Color →ₗ[ℂ] Multiplet := (rightIn 0).comp colorIn
def dIn : SMEpsilonTensor.Color →ₗ[ℂ] Multiplet := (rightIn 1).comp colorIn
def nIn : ℂ →ₗ[ℂ] Multiplet := (rightIn 0).comp leptonIn
def eIn : ℂ →ₗ[ℂ] Multiplet := (rightIn 1).comp leptonIn

theorem phase_add (g : GaugeGroup) (y z : ℤ) : phase (y+z) g = phase y g * phase z g := by
  change (↑(g.2.2^(y+z)):ℂ) = ↑(g.2.2^y) * ↑(g.2.2^z)
  rw [zpow_add,Circle.coe_mul]

theorem right_basis (g : GaugeGroup) (i : Fin 2) :
    right (hom g) (Pi.single i 1) =
      phase (if i=0 then 3 else -3) g • (Pi.single i 1 : Two) := by
  ext j
  change (rightMatrix g).mulVec (Pi.single i 1) j = _
  simp [rightMatrix,Matrix.mulVec_single,phase,Circle.coeHom,Pi.single_apply]
  split_ifs <;> rfl

theorem left_action (g : GaugeGroup) (w : Two) : left (hom g) w = weak g w := rfl

theorem qIn_equivariant (g : GaugeGroup) (v : Quark) :
    fL (hom g) (qIn v) = qIn (quark g v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a w =>
      simp [fL,qIn,Representation.tprod_apply,colorIn_equivariant,left_action,
        quark,twist,TensorProduct.smul_tmul']
  | add a b ha hb => simpa only [map_add] using congrArg₂ (·+·) ha hb

theorem lIn_equivariant (g : GaugeGroup) (w : Two) :
    fL (hom g) (lIn w) = lIn (lepton g w) := by
  simp [fL,lIn,Representation.tprod_apply,leptonIn_equivariant,left_action,
    lepton,twist,TensorProduct.smul_tmul']
  have he : leptonIn (phase (-3) g) = phase (-3) g • leptonIn 1 := by
    simpa only [smul_eq_mul,mul_one] using leptonIn.map_smul (phase (-3) g) 1
  rw [he]

theorem rightIn_equivariant (g : GaugeGroup) (i : Fin 2) (v : Four) :
    fR (hom g) (rightIn i v) =
      rightIn i (phase (if i=0 then 3 else -3) g • four (hom g) v) := by
  simp [fR,rightIn,Representation.tprod_apply,right_basis,TensorProduct.smul_tmul']

theorem uIn_equivariant (g : GaugeGroup) (v : SMEpsilonTensor.Color) :
    fR (hom g) (uIn v) = uIn (upRight g v) := by
  rw [uIn,LinearMap.comp_apply,rightIn_equivariant,colorIn_equivariant]
  change rightIn 0 (phase 3 g • colorIn (phase 1 g • color g v)) =
    rightIn 0 (colorIn (phase 4 g • color g v))
  simp only [map_smul,smul_smul]
  rw [← phase_add]
  rfl

theorem dIn_equivariant (g : GaugeGroup) (v : SMEpsilonTensor.Color) :
    fR (hom g) (dIn v) = dIn (downRight g v) := by
  rw [dIn,LinearMap.comp_apply,rightIn_equivariant,colorIn_equivariant]
  change rightIn 1 (phase (-3) g • colorIn (phase 1 g • color g v)) =
    rightIn 1 (colorIn (phase (-2) g • color g v))
  simp only [map_smul,smul_smul]
  rw [← phase_add]
  rfl

theorem nIn_equivariant (g : GaugeGroup) (s : ℂ) : fR (hom g) (nIn s) = nIn s := by
  rw [nIn,LinearMap.comp_apply,rightIn_equivariant,leptonIn_equivariant]
  change rightIn 0 (phase 3 g • leptonIn (phase (-3) g * s)) = rightIn 0 (leptonIn s)
  rw [← smul_eq_mul]
  simp only [map_smul,smul_smul]
  rw [← phase_add]
  simp [phase]

theorem eIn_equivariant (g : GaugeGroup) (s : ℂ) :
    fR (hom g) (eIn s) = eIn (electronRight g s) := by
  rw [eIn,LinearMap.comp_apply,rightIn_equivariant,leptonIn_equivariant]
  change rightIn 1 (phase (-3) g • leptonIn (phase (-3) g * s)) =
    rightIn 1 (leptonIn (phase (-6) g • s))
  rw [← smul_eq_mul]
  simp only [map_smul,smul_smul]
  rw [← phase_add]
  rfl

/-- Coordinate equivalence, not merely a count of dimensions. -/
def quarkArrayEquiv : Quark ≃ₗ[ℂ] (Fin 3 → Two) :=
  (TensorProduct.piLeft ℂ Two (fun _ : Fin 3 => ℂ)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.lid ℂ Two)

@[simp] theorem quarkArray_tmul (v : SMEpsilonTensor.Color) (w : Two) (a : Fin 3) (i : Fin 2) :
    quarkArrayEquiv (v ⊗ₜ[ℂ] w) a i = v a * w i := by
  simp [quarkArrayEquiv,TensorProduct.piLeft,TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

theorem array_qIn (v : Quark) (a : Index) (i : Fin 2) :
    arrayEquiv (qIn v) (indexEquiv a) i =
      Sum.elim (fun b => quarkArrayEquiv v b i) (fun _ => 0) a := by
  induction v using TensorProduct.inductionOn with
  | tmul c w => cases a <;> simp [qIn]
  | add v w hv hw => cases a <;> simp [hv,hw]

theorem array_lIn (w : Two) (a : Index) (i : Fin 2) :
    arrayEquiv (lIn w) (indexEquiv a) i = Sum.elim (fun _ => 0) (fun _ => w i) a := by
  cases a <;> simp [lIn]

theorem array_rightIn (v : Four) (i j : Fin 2) (a : Fin 4) :
    arrayEquiv (rightIn i v) a j = v a * (Pi.single i (1:ℂ) : Two) j := by
  simp [rightIn]

abbrev LeftComponents := Quark × Two
abbrev RightComponents := SMEpsilonTensor.Color × SMEpsilonTensor.Color × ℂ × ℂ

def leftJoin (x : LeftComponents) : Multiplet := qIn x.1 + lIn x.2
def rightJoin (x : RightComponents) : Multiplet :=
  uIn x.1 + dIn x.2.1 + nIn x.2.2.1 + eIn x.2.2.2

def leftSplit (v : Multiplet) : LeftComponents :=
  (quarkArrayEquiv.symm (fun a => arrayEquiv v (indexEquiv (Sum.inl a))),
   arrayEquiv v (indexEquiv (Sum.inr 0)))
def rightSplit (v : Multiplet) : RightComponents :=
  ((fun a => arrayEquiv v (indexEquiv (Sum.inl a)) 0),
   (fun a => arrayEquiv v (indexEquiv (Sum.inl a)) 1),
   arrayEquiv v (indexEquiv (Sum.inr 0)) 0,
   arrayEquiv v (indexEquiv (Sum.inr 0)) 1)

theorem leftSplit_join (x : LeftComponents) : leftSplit (leftJoin x) = x := by
  apply Prod.ext
  · apply quarkArrayEquiv.injective
    ext a i
    simp [leftSplit,leftJoin,array_qIn,array_lIn]
  · ext i
    simp [leftSplit,leftJoin,array_qIn,array_lIn]

theorem leftJoin_split (v : Multiplet) : leftJoin (leftSplit v) = v := by
  apply arrayEquiv.injective
  ext a i
  obtain ⟨a,rfl⟩ := indexEquiv.surjective a
  cases a with
  | inl a => simp [leftJoin,array_qIn,array_lIn,leftSplit]
  | inr a =>
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      simp [leftJoin,array_qIn,array_lIn,leftSplit]

theorem rightSplit_join (x : RightComponents) : rightSplit (rightJoin x) = x := by
  apply Prod.ext
  · ext a
    simp [rightSplit,rightJoin,uIn,dIn,nIn,eIn,array_rightIn]
  · apply Prod.ext
    · ext a
      simp [rightSplit,rightJoin,uIn,dIn,nIn,eIn,array_rightIn]
    · apply Prod.ext <;>
        simp [rightSplit,rightJoin,uIn,dIn,nIn,eIn,array_rightIn]

theorem rightJoin_split (v : Multiplet) : rightJoin (rightSplit v) = v := by
  apply arrayEquiv.injective
  ext a i
  obtain ⟨a,rfl⟩ := indexEquiv.surjective a
  cases a with
  | inl a => fin_cases i <;>
      simp [rightJoin,rightSplit,uIn,dIn,nIn,eIn,array_rightIn]
  | inr a =>
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      fin_cases i <;>
        simp [rightJoin,rightSplit,uIn,dIn,nIn,eIn,array_rightIn]

def leftSM : Representation ℂ GaugeGroup LeftComponents := quark.prod lepton
def rightSM : Representation ℂ GaugeGroup RightComponents :=
  upRight.prod (downRight.prod ((Representation.trivial ℂ GaugeGroup ℂ).prod electronRight))

def leftJoinMap : LeftComponents →ₗ[ℂ] Multiplet where
  toFun := leftJoin
  map_add' x y := by simp [leftJoin]; abel
  map_smul' c x := by simp [leftJoin,smul_add]
def rightJoinMap : RightComponents →ₗ[ℂ] Multiplet where
  toFun := rightJoin
  map_add' x y := by simp [rightJoin]; abel
  map_smul' c x := by
    simp only [rightJoin,Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,RingHom.id_apply]

def leftEquiv : LeftComponents ≃ₗ[ℂ] Multiplet :=
  { leftJoinMap with invFun := leftSplit, left_inv := leftSplit_join, right_inv := leftJoin_split }
def rightEquiv : RightComponents ≃ₗ[ℂ] Multiplet :=
  { rightJoinMap with invFun := rightSplit, left_inv := rightSplit_join, right_inv := rightJoin_split }

theorem leftJoin_equivariant (g : GaugeGroup) (x : LeftComponents) :
    fL (hom g) (leftJoin x) = leftJoin (leftSM g x) := by
  simp [leftJoin,leftSM,Representation.prod,qIn_equivariant,lIn_equivariant]

theorem rightJoin_equivariant (g : GaugeGroup) (x : RightComponents) :
    fR (hom g) (rightJoin x) = rightJoin (rightSM g x) := by
  simp [rightJoin,rightSM,Representation.prod,uIn_equivariant,dIn_equivariant,
    nIn_equivariant,eIn_equivariant]

theorem leftSplit_equivariant (g : GaugeGroup) (v : Multiplet) :
    leftSplit (fL (hom g) v) = leftSM g (leftSplit v) := by
  apply leftEquiv.injective
  change leftJoin (leftSplit (fL (hom g) v)) = leftJoin (leftSM g (leftSplit v))
  rw [leftJoin_split,← leftJoin_equivariant,leftJoin_split]

theorem rightSplit_equivariant (g : GaugeGroup) (v : Multiplet) :
    rightSplit (fR (hom g) v) = rightSM g (rightSplit v) := by
  apply rightEquiv.injective
  change rightJoin (rightSplit (fR (hom g) v)) = rightJoin (rightSM g (rightSplit v))
  rw [rightJoin_split,← rightJoin_equivariant,rightJoin_split]

def leftAdmission : Representation.IntertwiningMap leftSM (fL.comp hom) :=
  leftEquiv.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun g x => (leftJoin_equivariant g x).symm)
def rightAdmission : Representation.IntertwiningMap rightSM (fR.comp hom) :=
  rightEquiv.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun g x => (rightJoin_equivariant g x).symm)
def leftProjection : Representation.IntertwiningMap (fL.comp hom) leftSM :=
  leftEquiv.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ leftSplit_equivariant
def rightProjection : Representation.IntertwiningMap (fR.comp hom) rightSM :=
  rightEquiv.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ rightSplit_equivariant

theorem leptonIn_single (v : ℂ) : leptonIn v = Pi.single 3 v := by
  ext a
  obtain ⟨a,rfl⟩ := indexEquiv.surjective a
  cases a with
  | inl a =>
      rw [leptonIn_color,index_color]
      fin_cases a <;> simp
  | inr a => rw [leptonIn_lepton,index_lepton]; simp

theorem array_nIn (v : ℂ) : arrayEquiv (nIn v) = ComponentAdmission.neutralVEV v := by
  ext a i
  simp [nIn,array_rightIn,leptonIn_single,ComponentAdmission.neutralVEV,Pi.single_apply]
  split_ifs <;> simp_all

/-- Chi transforms in the same (4,1,2) representation as fR. -/
def chiAction (g : PSGroup) (x : ComponentAdmission.Array) : ComponentAdmission.Array :=
  arrayEquiv (fR g (arrayEquiv.symm x))

theorem neutralVEV_fixed (g : GaugeGroup) (v : ℂ) :
    chiAction (hom g) (ComponentAdmission.neutralVEV v) = ComponentAdmission.neutralVEV v := by
  rw [← array_nIn]
  simp [chiAction,nIn_equivariant]

/-- Transported representation on exactly the arrays consumed by previous contractions. -/
def arrayRepresentation (rho : Representation ℂ PSGroup Multiplet) :
    Representation ℂ PSGroup ComponentAdmission.Array where
  toFun g := arrayEquiv.toLinearMap.comp ((rho g).comp arrayEquiv.symm.toLinearMap)
  map_one' := by ext x a i; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply]

def chiRepresentation := arrayRepresentation fR

theorem array_intertwines (rho : Representation ℂ PSGroup Multiplet)
    (g : PSGroup) (v : Multiplet) :
    arrayEquiv (rho g v) = arrayRepresentation rho g (arrayEquiv v) := by
  simp [arrayRepresentation]

theorem chiRepresentation_neutral (g : GaugeGroup) (v : ℂ) :
    chiRepresentation (hom g) (ComponentAdmission.neutralVEV v) = ComponentAdmission.neutralVEV v :=
  neutralVEV_fixed g v

theorem leftProjection_admission (x : LeftComponents) : leftProjection (leftAdmission x) = x :=
  leftSplit_join x
theorem rightProjection_admission (x : RightComponents) : rightProjection (rightAdmission x) = x :=
  rightSplit_join x

theorem colorIn_single (a : Fin 3) (z : ℂ) :
    colorIn (Pi.single a z) = Pi.single a.castSucc z := by
  ext b
  obtain ⟨b,rfl⟩ := indexEquiv.surjective b
  cases b with
  | inl b =>
      rw [colorIn_color,index_color]
      fin_cases a <;> fin_cases b <;> simp
  | inr b =>
      rw [colorIn_lepton,index_lepton]
      fin_cases a <;> simp

theorem array_dIn_single (a : Fin 3) (z : ℂ) :
    arrayEquiv (dIn (Pi.single a z)) = Pi.single a.castSucc (Pi.single 1 z) := by
  ext b i
  simp [dIn,array_rightIn,colorIn_single,Pi.single_apply]
  split_ifs <;> simp_all

theorem leftAdmission_projection (v : Multiplet) : leftAdmission (leftProjection v) = v :=
  leftJoin_split v
theorem rightAdmission_projection (v : Multiplet) : rightAdmission (rightProjection v) = v :=
  rightJoin_split v
theorem leftAdmission_injective : Function.Injective leftAdmission := leftEquiv.injective
theorem rightAdmission_injective : Function.Injective rightAdmission := rightEquiv.injective

end
end GUT.PatiSalam.ComponentRepresentations
