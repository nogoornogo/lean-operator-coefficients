import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Math.RepresentationTheory.SU2.SU2ExteriorBlocks
import Math.RepresentationTheory.Exterior.ComplementaryExteriorDuality
import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.RepresentationTheory.Decomposition.ExternalIrreducibleMatch
import Math.RepresentationTheory.Constructions.FiniteProductHomSupport
import Math.RepresentationTheory.SU2.SU2FiniteCoupling
import Math.RepresentationTheory.Decomposition.ExternalTensorDual
import Math.LinearAlgebra.Symmetric.SymmetricPowerLowDegree
import Math.LinearAlgebra.Tensor.TensorDeterminant

/-! Complete exterior branching for two independently acting SU2 doublets.
Both degree-two branches, including the nonsinglet in either factor, are
retained. The Cauchy maps stay opaque at their consumer boundary. -/
namespace Math.SU2PairExterior
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars ExternalInvariantTensor
open scoped TensorProduct

attribute [local irreducible] TopExteriorCauchy.map

abbrev left := SU2ExteriorBlocks.left
abbrev right := SU2ExteriorBlocks.right
abbrev tensor := left.tprod right
abbrev PairCarrier (a b : ℕ) := Sym[ℂ]^a Doublet ⊗[ℂ] Sym[ℂ]^b Doublet

@[reducible] local instance (a b : ℕ) : AddCommGroup (PairCarrier a b) := inferInstance
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] Doublet) := inferInstance

abbrev pair (a b : ℕ) : Representation ℂ (Group × Group) (PairCarrier a b) :=
  external (doublet.symmetricPower a) (doublet.symmetricPower b)

local instance pairIrreducible (a b : ℕ) : IsIrreducible (pair a b) := by
  change IsIrreducible (ExternalTensorProduct.externalTprod
    (doublet.symmetricPower a) (doublet.symmetricPower b))
  exact ProductIrreducibility.externalTprod_isIrreducible _ _

def rightZero (a : ℕ) : Representation.Equiv (pair a 0) (left.symmetricPower a) :=
  (externalEquiv (.refl (doublet.symmetricPower a))
    (SymmetricPowerLowDegree.representationZeroEquiv doublet)).trans
    { toLinearEquiv := TensorProduct.rid ℂ (Sym[ℂ]^a Doublet)
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro x z
        change z • (doublet.symmetricPower a) g.1 x = (left.symmetricPower a) g (z • x)
        exact (map_smul _ z x).symm }

def leftZero (b : ℕ) : Representation.Equiv (pair 0 b) (right.symmetricPower b) :=
  (externalEquiv (SymmetricPowerLowDegree.representationZeroEquiv doublet)
    (.refl (doublet.symmetricPower b))).trans
    { toLinearEquiv := TensorProduct.lid ℂ (Sym[ℂ]^b Doublet)
      isIntertwining' g := by
        apply TensorProduct.ext'
        intro z x
        change z • (doublet.symmetricPower b) g.2 x = (right.symmetricPower b) g (z • x)
        exact (map_smul _ z x).symm }

theorem pair_equiv_iff (a b c d : ℕ) :
    Nonempty (Representation.Equiv (pair a b) (pair c d)) ↔ a=c ∧ b=d := by
  rw [ExternalIrreducibleMatch.equiv_iff]
  simp only [symmetricPower_eq,TauCeti.SU2.nonempty_equiv_symPower_iff]

theorem pair_dimension (a b : ℕ) : Module.finrank ℂ (PairCarrier a b)=(a+1)*(b+1) := by
  rw [Module.finrank_tensorProduct,TauCeti.SU2.finrank_symPower,TauCeti.SU2.finrank_symPower]

def basis := Pi.basisFun ℂ (Fin 2)

theorem left_det (g : Group × Group) : LinearMap.det (left g)=1 := by
  change LinearMap.det (Matrix.toLin' (g.1 : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.1.prop.2

theorem right_det (g : Group × Group) : LinearMap.det (right g)=1 := by
  change LinearMap.det (Matrix.toLin' (g.2 : Matrix (Fin 2) (Fin 2) ℂ))=1
  rw [LinearMap.det_toLin']
  exact g.2.prop.2

def leftColumn : IntertwiningMap (left.symmetricPower 2) (tensor.exteriorPower 2) :=
  ((Representation.TensorProduct.comm right left).exteriorPower 2).toIntertwiningMap.comp
    (TopExteriorCauchy.intertwiner basis right left right_det)

def rightColumn : IntertwiningMap (right.symmetricPower 2) (tensor.exteriorPower 2) :=
  TopExteriorCauchy.intertwiner basis left right left_det

theorem leftColumn_injective : Function.Injective leftColumn :=
  ((Representation.TensorProduct.comm right left).exteriorPower 2).injective.comp
    (SU2ExteriorBlocks.column_injective basis)

theorem rightColumn_injective : Function.Injective rightColumn :=
  SU2ExteriorBlocks.column_injective basis

def squareDegree (i : Fin 2) : ℕ × ℕ := if i=0 then (2,0) else (0,2)
abbrev SquareCarrier (i : Fin 2) := PairCarrier (squareDegree i).1 (squareDegree i).2
abbrev squarePiece (i : Fin 2) := pair (squareDegree i).1 (squareDegree i).2

def squareMap (i : Fin 2) : IntertwiningMap (squarePiece i) (tensor.exteriorPower 2) :=
  Fin.cases (leftColumn.comp (rightZero 2).toIntertwiningMap)
    (fun j => by
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      exact rightColumn.comp (leftZero 2).toIntertwiningMap) i

theorem squareMap_injective (i : Fin 2) : Function.Injective (squareMap i) := by
  fin_cases i
  · exact leftColumn_injective.comp (rightZero 2).injective
  · exact rightColumn_injective.comp (leftZero 2).injective

def squareAssemble : IntertwiningMap (FiniteBlockHom.action squarePiece) (tensor.exteriorPower 2) :=
  DistinctIrreducibleAssembly.assemble squarePiece (tensor.exteriorPower 2) squareMap

theorem squareAssemble_injective : Function.Injective squareAssemble := by
  apply DistinctIrreducibleAssembly.injective_of_inequivalent squarePiece (tensor.exteriorPower 2)
  · intro i hz
    let : Nontrivial (SquareCarrier i) := IsIrreducible.nontrivial (ρ := squarePiece i) inferInstance
    obtain ⟨x,hx⟩ := exists_ne (0 : SquareCarrier i)
    apply hx
    apply squareMap_injective i
    rw [hz]
    rfl
  · intro i j hij
    rw [pair_equiv_iff]
    fin_cases i <;> fin_cases j <;> simp_all [squareDegree]

theorem squareAssemble_surjective : Function.Surjective squareAssemble := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp squareAssemble_injective
  rw [Module.finrank_pi_fintype,Fin.sum_univ_two]
  change Module.finrank ℂ (PairCarrier 2 0)+Module.finrank ℂ (PairCarrier 0 2)=_
  rw [pair_dimension,pair_dimension,exteriorPower.finrank_eq,Module.finrank_tensorProduct]
  norm_num [Doublet,Nat.choose_two_right]

/-- Complete joint branching, rather than two selected injections. -/
def squareEquiv : Representation.Equiv (FiniteBlockHom.action squarePiece) (tensor.exteriorPower 2) :=
  squareAssemble.ofBijective ⟨squareAssemble_injective,squareAssemble_surjective⟩

def pairSelfDual (a b : ℕ) : Representation.Equiv (pair a b) (pair a b).dual :=
  (externalEquiv (SU2FiniteCoupling.selfDual a) (SU2FiniteCoupling.selfDual b)).trans
    (ExternalTensorDual.equiv (doublet.symmetricPower a) (doublet.symmetricPower b))

def zeroEquiv : Representation.Equiv (tensor.exteriorPower 0) (pair 0 0) :=
  tensor.exteriorPowerZeroEquiv.trans
    ((rightZero 0).trans (SymmetricPowerLowDegree.representationZeroEquiv left)).symm

def pairOne : Representation.Equiv (pair 1 1) tensor :=
  externalEquiv (SymmetricPowerLowDegree.representationOneEquiv doublet)
    (SymmetricPowerLowDegree.representationOneEquiv doublet)

def oneEquiv : Representation.Equiv (tensor.exteriorPower 1) (pair 1 1) :=
  tensor.exteriorPowerOneEquiv.trans pairOne.symm

theorem tensor_dimension : Module.finrank ℂ (Doublet ⊗[ℂ] Doublet)=4 := by
  rw [Module.finrank_tensorProduct]
  norm_num [Doublet]

theorem tensor_det (g : Group × Group) : LinearMap.det (tensor g)=1 :=
  TensorDeterminant.map_one basis basis (left g) (right g) (left_det g) (right_det g)

def volume := Module.Basis.exteriorPowerTopEquiv (Module.finBasis ℂ (Doublet ⊗[ℂ] Doublet))

def complement {n m : ℕ} (h : n+m=4) :
    Representation.Equiv (tensor.exteriorPower n) (tensor.exteriorPower m).dual :=
  ComplementaryExteriorDuality.equiv tensor tensor_det volume (by rw [tensor_dimension]; exact h)

def threeEquiv : Representation.Equiv (tensor.exteriorPower 3) (pair 1 1) :=
  (complement (by rfl : 3+1=4)).trans
    ((SplitRepresentationProjection.dualEquiv oneEquiv).trans (pairSelfDual 1 1).symm)

def fourEquiv : Representation.Equiv (tensor.exteriorPower 4) (pair 0 0) :=
  (complement (by rfl : 4+0=4)).trans
    ((SplitRepresentationProjection.dualEquiv zeroEquiv).trans (pairSelfDual 0 0).symm)

theorem pair_hom_iff (a b c d : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (pair a b) (pair c d)) ↔ a=c ∧ b=d := by
  constructor
  · rintro ⟨f,hf⟩
    exact (pair_equiv_iff a b c d).mp
      ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨IntertwiningMap.id _,?_⟩
    intro he
    let : Nontrivial (PairCarrier a b) := IsIrreducible.nontrivial (ρ := pair a b) inferInstance
    obtain ⟨x,hx⟩ := exists_ne (0 : PairCarrier a b)
    exact hx (DFunLike.congr_fun he x)

theorem target_along {n u v : ℕ}
    (e : Representation.Equiv (tensor.exteriorPower n) (pair u v)) (a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (tensor.exteriorPower n) (pair a b)) ↔ u=a ∧ v=b :=
  (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv e (.refl (pair a b)))).trans
    (pair_hom_iff u v a b)

theorem square_target_iff (a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (tensor.exteriorPower 2) (pair a b)) ↔
      (a=2 ∧ b=0) ∨ (a=0 ∧ b=2) := by
  rw [SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv squareEquiv.symm
    (.refl (pair a b))),FiniteProductHomSupport.allowed_iff]
  simp_rw [pair_hom_iff]
  simp [Fin.exists_fin_two,squareDegree,eq_comm]

theorem high_zero (n : ℕ) (hn : 4<n) (a b : ℕ)
    (f : IntertwiningMap (tensor.exteriorPower n) (pair a b)) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := exteriorPower.eq_zero_of_finrank_lt n (by rw [tensor_dimension]; exact hn) x
  rw [hx,map_zero]
  rfl

/-- Complete positive joint occurrence rule at every exterior degree. -/
theorem target_iff (n a b : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap (tensor.exteriorPower n) (pair a b)) ↔
      ((n=0 ∨ n=4) ∧ a=0 ∧ b=0) ∨
      ((n=1 ∨ n=3) ∧ a=1 ∧ b=1) ∨
      (n=2 ∧ ((a=2 ∧ b=0) ∨ (a=0 ∧ b=2))) := by
  by_cases hn : n≤4
  · interval_cases n
    · simpa [eq_comm] using target_along zeroEquiv a b
    · simpa [eq_comm] using target_along oneEquiv a b
    · simpa using square_target_iff a b
    · simpa [eq_comm] using target_along threeEquiv a b
    · simpa [eq_comm] using target_along fourEquiv a b
  · constructor
    · rintro ⟨f,hf⟩
      exact (hf (high_zero n (by omega) a b f)).elim
    · intro h
      rcases h with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> omega

end
end Math.SU2PairExterior
