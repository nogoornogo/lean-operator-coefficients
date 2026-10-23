import Math.RepresentationTheory.SU2.SU2PairCoupling

/-! Complete finite joint decompositions assembled from the proved
doublet-pair exterior branches and positive Clebsch--Gordan paths. Repeated
copies retain their indices; no support or multiplicity premise is supplied. -/
namespace Math.SU2PairDecomposition
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars SU2PairExterior

@[reducible] local instance (a b : ℕ) : AddCommGroup (PairCarrier a b) := inferInstance

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

structure Decomposition (rho : Representation ℂ (Group × Group) V) where
  Index : Type
  [finite : Fintype Index]
  [decidable : DecidableEq Index]
  weak : Index → ℕ
  spin : Index → ℕ
  equivalence : Representation.Equiv
    (FiniteBlockHom.action (fun i => pair (weak i) (spin i))) rho

attribute [instance] Decomposition.finite Decomposition.decidable

def singleton {A : Type*} [AddCommGroup A] [Module ℂ A] (rho : Representation ℂ (Group × Group) A) :
    Representation.Equiv (FiniteBlockHom.action (fun _ : Fin 1 => rho)) rho where
  toLinearEquiv :=
    { toFun := fun x => x 0
      invFun := fun x _ => x
      left_inv := by intro x; funext i; exact congrArg x (Subsingleton.elim _ _)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def atom (a b : ℕ) : Decomposition (pair a b) where
  Index := Fin 1
  weak := fun _ => a
  spin := fun _ => b
  equivalence := singleton _

variable {rho : Representation ℂ (Group × Group) V} {sigma : Representation ℂ (Group × Group) W}

def tensor (D : Decomposition rho) (E : Decomposition sigma) : Decomposition (rho.tprod sigma) where
  Index := Σ p : D.Index × E.Index,
    SU2PairCoupling.Index (D.weak p.1) (D.spin p.1) (E.weak p.2) (E.spin p.2)
  weak := fun p => SU2ClebschGordan.degree (D.weak p.1.1) (E.weak p.1.2) p.2.1
  spin := fun p => SU2ClebschGordan.degree (D.spin p.1.1) (E.spin p.1.2) p.2.2
  equivalence :=
    ((tensorEquiv D.equivalence.symm E.equivalence.symm).trans
      ((FiniteExternalProducts.diagonalEquivalence _ _).trans
        ((FiniteExternalProducts.along (fun p : D.Index × E.Index =>
          SU2PairCoupling.equivalence (D.weak p.1) (D.spin p.1) (E.weak p.2) (E.spin p.2))).trans
          (FiniteExternalProducts.flatten (fun p : D.Index × E.Index =>
            SU2PairCoupling.piece (D.weak p.1) (D.spin p.1) (E.weak p.2) (E.spin p.2)))))).symm

def Occurs (D : Decomposition rho) (a b : ℕ) : Prop := ∃ i, D.weak i=a ∧ D.spin i=b

theorem target_iff (D : Decomposition rho) (a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap rho (pair a b)) ↔ Occurs D a b := by
  rw [SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv D.equivalence.symm
    (.refl (pair a b))),FiniteProductHomSupport.allowed_iff]
  simp only [pair_hom_iff,Occurs]

theorem tensor_occurs_iff (D : Decomposition rho) (E : Decomposition sigma) (u v : ℕ) :
    Occurs (tensor D E) u v ↔
      ∃ a b c d, Occurs D a b ∧ Occurs E c d ∧
        SU2PairCoupling.Triangle a c u ∧ SU2PairCoupling.Triangle b d v := by
  change (∃ p : (Σ p : D.Index × E.Index,
      SU2PairCoupling.Index (D.weak p.1) (D.spin p.1) (E.weak p.2) (E.spin p.2)),
      SU2ClebschGordan.degree (D.weak p.1.1) (E.weak p.1.2) p.2.1=u ∧
      SU2ClebschGordan.degree (D.spin p.1.1) (E.spin p.1.2) p.2.2=v) ↔ _
  constructor
  · rintro ⟨⟨⟨i,j⟩,⟨r,s⟩⟩,hr,hs⟩
    exact ⟨_,_,_,_,⟨i,rfl,rfl⟩,⟨j,rfl,rfl⟩,
      (SU2PairCoupling.degree_exists_iff _ _ _).mp ⟨r,hr⟩,
      (SU2PairCoupling.degree_exists_iff _ _ _).mp ⟨s,hs⟩⟩
  · rintro ⟨a,b,c,d,⟨i,hi₁,hi₂⟩,⟨j,hj₁,hj₂⟩,hu,hv⟩
    rw [← hi₁,← hj₁] at hu
    rw [← hi₂,← hj₂] at hv
    obtain ⟨r,hr⟩ := (SU2PairCoupling.degree_exists_iff _ _ _).mpr hu
    obtain ⟨s,hs⟩ := (SU2PairCoupling.degree_exists_iff _ _ _).mpr hv
    exact ⟨⟨(i,j),(r,s)⟩,hr,hs⟩

def exteriorCount : ℕ → ℕ
  | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 1 | _+5 => 0

def exteriorLabel : (n : ℕ) → Fin (exteriorCount n) → ℕ × ℕ
  | 0,_ => (0,0) | 1,_ => (1,1) | 2,i => squareDegree i
  | 3,_ => (1,1) | 4,_ => (0,0) | _+5,i => Fin.elim0 i

abbrev exteriorPiece (n : ℕ) (i : Fin (exteriorCount n)) :=
  pair (exteriorLabel n i).1 (exteriorLabel n i).2

def highEquiv (k : ℕ) : Representation.Equiv
    (FiniteBlockHom.action (exteriorPiece (k+5))) (SU2PairExterior.tensor.exteriorPower (k+5)) where
  toLinearEquiv :=
    { toFun := fun _ => 0
      invFun := fun _ i => Fin.elim0 i
      left_inv := by intro x; funext i; exact Fin.elim0 i
      right_inv := by
        intro x
        exact (exteriorPower.eq_zero_of_finrank_lt (k+5)
          (by rw [tensor_dimension]; omega) x).symm
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
  isIntertwining' g := by ext x; simp

def exteriorEquiv : (n : ℕ) → Representation.Equiv
    (FiniteBlockHom.action (exteriorPiece n)) (SU2PairExterior.tensor.exteriorPower n)
  | 0 => (singleton _).trans zeroEquiv.symm
  | 1 => (singleton _).trans oneEquiv.symm
  | 2 => squareEquiv
  | 3 => (singleton _).trans threeEquiv.symm
  | 4 => (singleton _).trans fourEquiv.symm
  | k+5 => highEquiv k

def exterior (n : ℕ) : Decomposition (SU2PairExterior.tensor.exteriorPower n) where
  Index := Fin (exteriorCount n)
  weak := fun i => (exteriorLabel n i).1
  spin := fun i => (exteriorLabel n i).2
  equivalence := exteriorEquiv n

def CoreSupport (n a b : ℕ) : Prop :=
  ((n=0 ∨ n=4) ∧ a=0 ∧ b=0) ∨
  ((n=1 ∨ n=3) ∧ a=1 ∧ b=1) ∨
  (n=2 ∧ ((a=2 ∧ b=0) ∨ (a=0 ∧ b=2)))

theorem exterior_occurs_iff (n a b : ℕ) : Occurs (exterior n) a b ↔ CoreSupport n a b :=
  (target_iff (exterior n) a b).symm.trans (SU2PairExterior.target_iff n a b)

/-- Every path condition is positive: core branches and triangle/parity
conditions, with no residual Hom or signed coefficient extraction. -/
theorem exterior_pair_target_iff (n m u v : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap
      ((SU2PairExterior.tensor.exteriorPower n).tprod (SU2PairExterior.tensor.exteriorPower m))
      (pair u v)) ↔
      ∃ a b c d, CoreSupport n a b ∧ CoreSupport m c d ∧
        SU2PairCoupling.Triangle a c u ∧ SU2PairCoupling.Triangle b d v := by
  rw [target_iff (tensor (exterior n) (exterior m)),tensor_occurs_iff]
  simp_rw [exterior_occurs_iff]

/-- Three generation factors with their shared weak/spin actions. All
intermediate labels are retained, including nonsinglets. -/
theorem exterior_triple_target_iff (n m l u v : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap
      ((SU2PairExterior.tensor.exteriorPower n).tprod
        ((SU2PairExterior.tensor.exteriorPower m).tprod (SU2PairExterior.tensor.exteriorPower l)))
      (pair u v)) ↔
      ∃ a b c d, CoreSupport n a b ∧
        (∃ e f g h, CoreSupport m e f ∧ CoreSupport l g h ∧
          SU2PairCoupling.Triangle e g c ∧ SU2PairCoupling.Triangle f h d) ∧
        SU2PairCoupling.Triangle a c u ∧ SU2PairCoupling.Triangle b d v := by
  rw [target_iff (tensor (exterior n) (tensor (exterior m) (exterior l))),tensor_occurs_iff]
  simp_rw [exterior_occurs_iff,tensor_occurs_iff,exterior_occurs_iff]

end
end Math.SU2PairDecomposition
