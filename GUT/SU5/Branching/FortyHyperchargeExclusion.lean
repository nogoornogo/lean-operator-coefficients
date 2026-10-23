import GUT.SU5.Branching.ExoticHyperchargeBasis

open Physics

namespace GUT.SU5.FortyHyperchargeExclusion
set_option autoImplicit false
noncomputable section
open Math Representation Matter StandardModelEmbedding StandardSMGaugeTensor SMEpsilonTensor
open InvariantMassNormalForm ExoticHyperchargeBasis
open scoped TensorProduct
local instance : AddCommGroup Ten := inferInstance
abbrev FiveIndex := Fin 3 ⊕ Fin 2

def fiveBlockBasis : Module.Basis FiveIndex ℂ FundamentalBranching.Blocks :=
  (Pi.basisFun ℂ (Fin 3)).prod (Pi.basisFun ℂ (Fin 2))
def fiveBasis : Module.Basis FiveIndex ℂ Five :=
  fiveBlockBasis.map FundamentalBranching.fundamentalEquiv.toLinearEquiv.symm

def fiveWeight : FiveIndex → ℤ | .inl _ => -2 | .inr _ => 3

theorem five_basis_action (z : Circle) (i : FiveIndex) :
    fundamental (hom (1,1,z)) (fiveBasis i) = ((z^fiveWeight i : Circle) : ℂ) • fiveBasis i := by
  let e := FundamentalBranching.fundamentalEquiv
  apply e.toLinearEquiv.injective
  have he := DFunLike.congr_fun (e.isIntertwining' (1,1,z)) (fiveBasis i)
  change e (fundamental (hom (1,1,z)) (fiveBasis i)) = FundamentalBranching.blocksRho (1,1,z) (e (fiveBasis i)) at he
  change e (fundamental (hom (1,1,z)) (fiveBasis i)) = e (((z^fiveWeight i : Circle) : ℂ) • fiveBasis i)
  rw [he,map_smul]
  have hb (j : FiveIndex) : e (fiveBasis j) = fiveBlockBasis j :=
    e.toLinearEquiv.apply_symm_apply _
  rw [hb]
  rcases i with i | i <;>
    simp [fiveBlockBasis, FundamentalBranching.blocksRho, fiveWeight,
      twist, color, weak, phase]

abbrev ambient := fundamental.tprod ten
abbrev ambientBasis := fiveBasis.tensorProduct tenBasis

def coefficient (z : Circle) (i : FiveIndex × Index) : ℂ :=
  ((z^(fiveWeight i.1 + weight i.2) : Circle) : ℂ)

theorem ambient_action (z : Circle) (i : FiveIndex × Index) :
    ambient (hom (1,1,z)) (ambientBasis i) = coefficient z i • ambientBasis i := by
  rcases i with ⟨i,j⟩
  simp only [ambient, ambientBasis, Module.Basis.tensorProduct_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, five_basis_action, basis_action]
  simp [coefficient, zpow_add, Circle.coe_mul, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem coefficient_separated (i : FiveIndex × Index) (y : ℤ)
    (hy : y ∈ ([1,-4,6] : List ℤ)) : coefficient root i ≠ ((root^y : Circle) : ℂ) := by
  intro he
  have hc : ((fiveWeight i.1+weight i.2 : ℤ) : ZMod 31) = (y : ZMod 31) := by
    apply ZMod.injective_stdAddChar
    change ((ZMod.toCircle ((fiveWeight i.1+weight i.2 : ℤ) : ZMod 31) : Circle) : ℂ) = _
    exact ((congrArg (fun z : Circle => (z : ℂ))
      (root_zpow (fiveWeight i.1+weight i.2))).symm.trans he).trans
      (congrArg (fun z : Circle => (z : ℂ)) (root_zpow y))
  have hf : fiveWeight i.1 = -2 ∨ fiveWeight i.1 = 3 := by
    rcases i.1 with j | j
    · exact Or.inl rfl
    · exact Or.inr rfl
  have ht : weight i.2 = -4 ∨ weight i.2 = 1 ∨ weight i.2 = 6 := by
    rcases i.2 with j | j
    · exact Or.inl rfl
    · rcases j with j | j
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
  have hn : ((fiveWeight i.1+weight i.2 : ℤ) : ZMod 31) ≠ (y : ZMod 31) := by
    rcases hf with hf | hf <;> rcases ht with ht | ht | ht <;>
      rcases hy with hy | hy | hy <;> simp only [hf,ht,hy] <;> decide
  exact hn hc

theorem ambient_no_eigen (y : ℤ) (hy : y ∈ ([1,-4,6] : List ℤ))
    (v : Five ⊗[ℂ] Ten) (hv : ambient (hom (1,1,root)) v = ((root^y : Circle) : ℂ) • v) : v=0 := by
  apply ambientBasis.repr.injective
  ext s
  change ambientBasis.coord s v = 0
  have he : (ambientBasis.coord s).comp (ambient (hom (1,1,root))) =
      coefficient root s • ambientBasis.coord s := by
    apply ambientBasis.ext
    intro t
    simp only [LinearMap.comp_apply,ambient_action,map_smul,LinearMap.smul_apply]
    change coefficient root t * ambientBasis.repr (ambientBasis t) s =
      coefficient root s * ambientBasis.repr (ambientBasis t) s
    rw [ambientBasis.repr_self_apply]
    by_cases h : t=s
    · subst t; rfl
    · simp only [h,ite_false,mul_zero]
  have hc := DFunLike.congr_fun he v
  change ambientBasis.coord s (ambient (hom (1,1,root)) v) =
    coefficient root s * ambientBasis.coord s v at hc
  rw [hv,map_smul] at hc
  have hz : (coefficient root s - ((root^y : Circle) : ℂ)) * ambientBasis.coord s v = 0 := by
    linear_combination -hc
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (coefficient_separated s y hy))

abbrev Kernel := ExoticWedgeKernel.kernel.toSubmodule
local instance : AddCommGroup Kernel := inferInstance
local instance : Module ℂ Kernel := inferInstance
abbrev original : Representation ℂ GaugeGroup Kernel := ExoticWedgeKernel.kernel.toRepresentation.comp hom
abbrev forty : Representation ℂ GaugeGroup (Module.Dual ℂ Kernel) := original.dual

theorem original_no_eigen (y : ℤ) (hy : y ∈ ([1,-4,6] : List ℤ))
    (v : Kernel) (hv : original (1,1,root) v = ((root^y : Circle) : ℂ) • v) : v=0 := by
  apply Subtype.ext
  apply ambient_no_eigen y hy
  exact congrArg Subtype.val hv

theorem original_hom_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([1,-4,6] : List ℤ)) (f : IntertwiningMap r original) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply original_no_eigen y hy
  have hi := DFunLike.congr_fun (f.isIntertwining' (1,1,root)) v
  change f (r (1,1,root) v) = original (1,1,root) (f v) at hi
  rw [hr root v,map_smul] at hi
  exact hi.symm

theorem no_pairings_forty {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([1,-4,6] : List ℤ)) : Physics.BipartiteNormalForm.NoPairings r forty := by
  intro f
  let e := SplitRepresentationProjection.bidualEquiv original
  have he := original_hom_zero r y hr hy (e.symm.toIntertwiningMap.comp f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply e.symm.toLinearEquiv.injective
  have hz := DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap he) v
  simpa using hz

theorem forty_eq_actual_restriction : forty = ExoticWedgeKernel.representation.comp hom :=
  (SplitRepresentationProjection.dual_comp ExoticWedgeKernel.kernel.toRepresentation hom).symm

theorem selected_no_pairings :
    Physics.BipartiteNormalForm.NoPairings quark forty ∧
    Physics.BipartiteNormalForm.NoPairings upRight.dual forty ∧
    Physics.BipartiteNormalForm.NoPairings electronRight.dual forty :=
  ⟨no_pairings_forty quark 1 quark_hypercharge (by decide),
    no_pairings_forty upRight.dual (-4) upLeft_hypercharge (by decide),
    no_pairings_forty electronRight.dual 6 electronLeft_hypercharge (by decide)⟩

theorem original_shift_surjective (y : ℤ) (hy : y ∈ ([1,-4,6] : List ℤ)) :
    Function.Surjective (original (1,1,root) - ((root^y : Circle) : ℂ) •
      (LinearMap.id : Kernel →ₗ[ℂ] Kernel)) := by
  apply LinearMap.surjective_of_injective
  intro v w h
  have hz : (original (1,1,root) - ((root^y : Circle) : ℂ) • (LinearMap.id : Kernel →ₗ[ℂ] Kernel)) (v-w) = 0 := by
    rw [map_sub,h,sub_self]
  change original (1,1,root) (v-w) - ((root^y : Circle) : ℂ) • (v-w) = 0 at hz
  exact sub_eq_zero.mp (original_no_eigen y hy (v-w) (sub_eq_zero.mp hz))

theorem forty_no_opposite_eigen (y : ℤ) (hy : y ∈ ([-1,4,-6] : List ℤ))
    (phi : Module.Dual ℂ Kernel)
    (hv : forty (1,1,root) phi = ((root^y : Circle) : ℂ) • phi) : phi=0 := by
  have hn : -y ∈ ([1,-4,6] : List ℤ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    rcases hy with h | h | h <;> simp [h]
  have hinv : ((root^(-y) : Circle) : ℂ) * ((root^y : Circle) : ℂ) = 1 := by
    have h : root^(-y)*root^y = 1 := by simp
    exact congrArg (fun z : Circle => (z : ℂ)) h
  ext v
  obtain ⟨w,hw⟩ := original_shift_surjective (-y) hn v
  have hh := congrArg (fun f : Module.Dual ℂ Kernel => f (original (1,1,root) w)) hv
  change phi (original (1,1,root)⁻¹ (original (1,1,root) w)) =
    ((root^y : Circle) : ℂ) * phi (original (1,1,root) w) at hh
  have hh' : phi w = ((root^y : Circle) : ℂ) * phi (original (1,1,root) w) := by
    have hi := Representation.inv_self_apply original (1,1,root) w
    rw [hi] at hh
    exact hh
  have he : phi (original (1,1,root) w) = ((root^(-y) : Circle) : ℂ) * phi w := by
    rw [hh', ← mul_assoc,hinv,one_mul]
  rw [← hw]
  change phi (original (1,1,root) w - ((root^(-y) : Circle) : ℂ) • w) = 0
  rw [map_sub,map_smul,he]
  simp only [smul_eq_mul,sub_self]

theorem opposite_hom_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-1,4,-6] : List ℤ)) (f : IntertwiningMap r forty) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply forty_no_opposite_eigen y hy
  have hi := DFunLike.congr_fun (f.isIntertwining' (1,1,root)) v
  change f (r (1,1,root) v) = forty (1,1,root) (f v) at hi
  rw [hr root v,map_smul] at hi
  exact hi.symm

theorem opposite_hom_finrank_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-1,4,-6] : List ℤ)) :
    Module.finrank ℂ (IntertwiningMap r forty) = 0 := by
  have : Subsingleton (IntertwiningMap r forty) := ⟨fun f g =>
    (opposite_hom_zero r y hr hy f).trans (opposite_hom_zero r y hr hy g).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end GUT.SU5.FortyHyperchargeExclusion

