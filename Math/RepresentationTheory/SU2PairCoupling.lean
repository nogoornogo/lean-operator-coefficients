import Math.RepresentationTheory.SU2PairExterior
import Math.RepresentationTheory.SU2ClebschGordan
import Math.RepresentationTheory.FiniteExternalProducts

/-! Complete positive coupling of joint weak/spin labels. Clebsch--Gordan
is applied independently to the two factors, retaining both intermediate
labels and all summands. No multiplicity arithmetic is evaluated. -/
namespace Math.SU2PairCoupling
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeakDoubletScalars SU2PairExterior
open scoped TensorProduct

@[reducible] local instance (a b : ℕ) : AddCommGroup (PairCarrier a b) := inferInstance

abbrev Index (a b c d : ℕ) := SU2ClebschGordan.Index a c × SU2ClebschGordan.Index b d
abbrev piece (a b c d : ℕ) (i : Index a b c d) :=
  pair (SU2ClebschGordan.degree a c i.1) (SU2ClebschGordan.degree b d i.2)

/-- Complete tensor decomposition, with a product of finite SU2 path labels. -/
def equivalence (a b c d : ℕ) : Representation.Equiv
    ((pair a b).tprod (pair c d)) (FiniteBlockHom.action (piece a b c d)) :=
  (regroupPair (doublet.symmetricPower a) (doublet.symmetricPower c)
    (doublet.symmetricPower b) (doublet.symmetricPower d)).trans
    ((externalEquiv (SU2ClebschGordan.equivalence a c).symm
      (SU2ClebschGordan.equivalence b d).symm).trans
        (FiniteExternalProducts.equivalence (SU2ClebschGordan.summand a c)
          (SU2ClebschGordan.summand b d)))

def Triangle (a b c : ℕ) : Prop :=
  c≤a+b ∧ a≤b+c ∧ b≤a+c ∧ (a+b+c)%2=0

theorem degree_exists_iff (a b c : ℕ) :
    (∃ i : SU2ClebschGordan.Index a b, SU2ClebschGordan.degree a b i=c) ↔ Triangle a b c := by
  simp_rw [SU2ClebschGordan.degree_eq]
  constructor
  · rintro ⟨i,hi⟩
    have hh := i.isLt
    unfold Triangle
    omega
  · intro h
    unfold Triangle at h
    refine ⟨⟨(a+b-c)/2,by omega⟩,?_⟩
    dsimp
    omega

theorem target_iff (a b c d u v : ℕ) :
    SelectionCriteria.Allowed (IntertwiningMap ((pair a b).tprod (pair c d)) (pair u v)) ↔
      Triangle a c u ∧ Triangle b d v := by
  rw [SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv (equivalence a b c d)
    (.refl (pair u v))),FiniteProductHomSupport.allowed_iff]
  change (∃ i : Index a b c d,
    SelectionCriteria.Allowed (IntertwiningMap (pair (SU2ClebschGordan.degree a c i.1)
      (SU2ClebschGordan.degree b d i.2)) (pair u v))) ↔ _
  simp_rw [pair_hom_iff]
  rw [← degree_exists_iff,← degree_exists_iff]
  constructor
  · rintro ⟨⟨i,j⟩,hi,hj⟩
    exact ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    exact ⟨(i,j),hi,hj⟩

end
end Math.SU2PairCoupling
