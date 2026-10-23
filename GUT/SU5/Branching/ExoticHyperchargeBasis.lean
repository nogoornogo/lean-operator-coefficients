import GUT.SU5.Representations.ExoticSymmetricKernel
import GUT.SU5.Branching.ExteriorSquare
import GUT.SU5.SelectionRules.InvariantMassNormalForm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Physics

namespace GUT.SU5.ExoticHyperchargeBasis
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Math Representation Matter StandardModelEmbedding ExteriorSquareBranching
open StandardSMGaugeTensor SMEpsilonTensor InvariantMassNormalForm
local instance : AddCommGroup Quark := inferInstance
local instance : AddCommGroup Ten := inferInstance
abbrev Index := Fin 3 ⊕ ((Fin 3 × Fin 2) ⊕ Unit)

def blockBasis : Module.Basis Index ℂ Blocks :=
  (Pi.basisFun ℂ (Fin 3)).dualBasis.prod
    (((Pi.basisFun ℂ (Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin 2))).prod
      (Module.Basis.singleton Unit ℂ).dualBasis)
def tenBasis : Module.Basis Index ℂ Ten := blockBasis.map tenEquiv.toLinearEquiv.symm

def weight : Index → ℤ
  | .inl _ => -4
  | .inr (.inl _) => 1
  | .inr (.inr _) => 6

theorem basis_action (z : Circle) (i : Index) :
    ten (hom (1,1,z)) (tenBasis i) = ((z^weight i : Circle) : ℂ) • tenBasis i := by
  apply tenEquiv.toLinearEquiv.injective
  have he := DFunLike.congr_fun (tenEquiv.isIntertwining' (1,1,z)) (tenBasis i)
  change tenEquiv (ten (hom (1,1,z)) (tenBasis i)) = blocksRho (1,1,z) (tenEquiv (tenBasis i)) at he
  change tenEquiv (ten (hom (1,1,z)) (tenBasis i)) = tenEquiv (((z^weight i : Circle) : ℂ) • tenBasis i)
  rw [he, map_smul]
  have hb (j : Index) : tenEquiv (tenBasis j) = blockBasis j := by
    exact tenEquiv.toLinearEquiv.apply_symm_apply (blockBasis j)
  rw [hb]
  rcases i with i | i
  · change blocksRho (1,1,z) (blockBasis (.inl i)) = _
    have hz := upLeft_hypercharge z ((Pi.basisFun ℂ (Fin 3)).dualBasis i)
    simpa [blockBasis, blocksRho, weight] using congrArg
      (fun u : Module.Dual ℂ Color => (u, ((0 : Quark), (0 : Module.Dual ℂ ℂ)))) hz
  · rcases i with i | i
    · simp [blockBasis, blocksRho, weight, quark_hypercharge z]
    · have hz := electronLeft_hypercharge z ((Module.Basis.singleton Unit ℂ).dualBasis i)
      simpa [blockBasis, blocksRho, weight] using congrArg
        (fun e : Module.Dual ℂ ℂ => ((0 : Module.Dual ℂ Color), ((0 : Quark), e))) hz

def root : Circle := ZMod.toCircle (1 : ZMod 31)

theorem root_zpow (k : ℤ) : root^k = ZMod.toCircle (k : ZMod 31) := by
  simpa [root] using ((ZMod.toCircle (N := 31)).map_zsmul_eq_zpow k (1 : ZMod 31)).symm

def coefficient (z : Circle) (s : Sym Index 2) : ℂ :=
  ((s : Multiset Index).map (fun i => ((z^weight i : Circle) : ℂ))).prod

abbrev symmetricBasis := tenBasis.symmetricPower 2

theorem symmetric_action (z : Circle) (s : Sym Index 2) :
    (ten.symmetricPower 2) (hom (1,1,z)) (symmetricBasis s) =
      coefficient z s • symmetricBasis s :=
  Module.Basis.map_symmetricPower_of_apply tenBasis
    (ten (hom (1,1,z))) (fun i => ((z^weight i : Circle) : ℂ)) (basis_action z) s

/-- The six relevant Q/U/E and opposite hypercharges are absent from Sym² ten. -/
theorem coefficient_separated (s : Sym Index 2) (y : ℤ)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    coefficient root s ≠ ((root^y : Circle) : ℂ) := by
  obtain ⟨f,rfl⟩ := TauCeti.Sym.ofFn_surjective s
  intro h
  have he : ((root^(weight (f 0)+weight (f 1)) : Circle) : ℂ) =
      ((root^y : Circle) : ℂ) := by
    simpa [coefficient, TauCeti.Sym.coe_ofFn, List.map_ofFn, List.prod_ofFn,
      Fin.prod_univ_two, zpow_add, Circle.coe_mul] using h
  have hc : ((weight (f 0)+weight (f 1) : ℤ) : ZMod 31) = (y : ZMod 31) := by
    apply ZMod.injective_stdAddChar
    change ((ZMod.toCircle ((weight (f 0)+weight (f 1) : ℤ) : ZMod 31) : Circle) : ℂ) =
      ((ZMod.toCircle (y : ZMod 31) : Circle) : ℂ)
    exact ((congrArg (fun z : Circle => (z : ℂ))
      (root_zpow (weight (f 0)+weight (f 1)))).symm.trans he).trans
      (congrArg (fun z : Circle => (z : ℂ)) (root_zpow y))
  have hw (i : Index) : weight i = -4 ∨ weight i = 1 ∨ weight i = 6 := by
    rcases i with i | i
    · exact Or.inl rfl
    · rcases i with i | i
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have h0 := hw (f 0)
  have h1 := hw (f 1)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  have hn : ((weight (f 0)+weight (f 1) : ℤ) : ZMod 31) ≠ (y : ZMod 31) := by
    rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
      rcases hy with hy | hy | hy | hy | hy | hy <;>
      simp only [h0,h1,hy] <;> decide
  exact hn hc

theorem symmetric_no_eigen (y : ℤ) (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ))
    (v : Sym[ℂ]^2 Ten)
    (hv : (ten.symmetricPower 2) (hom (1,1,root)) v = ((root^y : Circle) : ℂ) • v) : v=0 := by
  apply symmetricBasis.repr.injective
  ext s
  change symmetricBasis.coord s v = 0
  have he : (symmetricBasis.coord s).comp ((ten.symmetricPower 2) (hom (1,1,root))) =
      coefficient root s • symmetricBasis.coord s := by
    apply symmetricBasis.ext
    intro t
    simp only [LinearMap.comp_apply, symmetric_action, map_smul, LinearMap.smul_apply]
    change coefficient root t * symmetricBasis.repr (symmetricBasis t) s =
      coefficient root s * symmetricBasis.repr (symmetricBasis t) s
    rw [symmetricBasis.repr_self_apply]
    by_cases h : t=s
    · subst t; rfl
    · simp only [h, ite_false, mul_zero]
  have hc := DFunLike.congr_fun he v
  change symmetricBasis.coord s ((ten.symmetricPower 2) (hom (1,1,root)) v) =
    coefficient root s * symmetricBasis.coord s v at hc
  rw [hv,map_smul] at hc
  have hz : (coefficient root s - ((root^y : Circle) : ℂ)) * symmetricBasis.coord s v = 0 := by
    linear_combination -hc
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (coefficient_separated s y hy))

theorem fifty_hom_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ)
    (hr : HasHypercharge r y) (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ))
    (f : IntertwiningMap r (ExoticSymmetricKernel.representation.comp hom)) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply symmetric_no_eigen y hy
  have hi := DFunLike.congr_fun (f.isIntertwining' (1,1,root)) v
  change f (r (1,1,root) v) = (ExoticSymmetricKernel.representation.comp hom) (1,1,root) (f v) at hi
  rw [hr root v,map_smul] at hi
  exact (congrArg Subtype.val hi).symm

abbrev Fifty := ExoticSymmetricKernel.kernel.toSubmodule
local instance : AddCommGroup Fifty := inferInstance
local instance : Module ℂ Fifty := inferInstance
abbrev fifty : Representation ℂ GaugeGroup Fifty := ExoticSymmetricKernel.representation.comp hom

theorem fifty_no_eigen (y : ℤ) (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ))
    (v : Fifty) (hv : fifty (1,1,root) v = ((root^y : Circle) : ℂ) • v) : v=0 := by
  apply Subtype.ext
  apply symmetric_no_eigen y hy
  exact congrArg Subtype.val hv

theorem fifty_shift_surjective (y : ℤ) (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    Function.Surjective (fifty (1,1,root) - ((root^y : Circle) : ℂ) • (LinearMap.id : Fifty →ₗ[ℂ] Fifty)) := by
  apply LinearMap.surjective_of_injective
  intro v w h
  have hz : (fifty (1,1,root) - ((root^y : Circle) : ℂ) • (LinearMap.id : Fifty →ₗ[ℂ] Fifty)) (v-w) = 0 := by
    rw [map_sub,h,sub_self]
  change fifty (1,1,root) (v-w) - ((root^y : Circle) : ℂ) • (v-w) = 0 at hz
  exact sub_eq_zero.mp (fifty_no_eigen y hy (v-w) (sub_eq_zero.mp hz))

theorem fifty_dual_no_eigen (y : ℤ) (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ))
    (phi : Module.Dual ℂ Fifty)
    (hv : fifty.dual (1,1,root) phi = ((root^y : Circle) : ℂ) • phi) : phi=0 := by
  have hn : -y ∈ ([-6,-4,-1,1,4,6] : List ℤ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    rcases hy with h | h | h | h | h | h <;> simp [h]
  have hinv : ((root^(-y) : Circle) : ℂ) * ((root^y : Circle) : ℂ) = 1 := by
    have h : root^(-y)*root^y = 1 := by simp
    exact congrArg (fun z : Circle => (z : ℂ)) h
  ext v
  obtain ⟨w,hw⟩ := fifty_shift_surjective (-y) hn v
  have hh := congrArg (fun f : Module.Dual ℂ Fifty => f (fifty (1,1,root) w)) hv
  change phi (fifty (1,1,root)⁻¹ (fifty (1,1,root) w)) =
    ((root^y : Circle) : ℂ) * phi (fifty (1,1,root) w) at hh
  have hh' : phi w = ((root^y : Circle) : ℂ) * phi (fifty (1,1,root) w) := by
    have hi : fifty (1,1,root)⁻¹ (fifty (1,1,root) w) = w := by
      exact Representation.inv_self_apply fifty (1,1,root) w
    rw [hi] at hh
    exact hh
  have he : phi (fifty (1,1,root) w) = ((root^(-y) : Circle) : ℂ) * phi w := by
    rw [hh', ← mul_assoc,hinv,one_mul]
  rw [← hw]
  change phi (fifty (1,1,root) w - ((root^(-y) : Circle) : ℂ) • w) = 0
  rw [map_sub,map_smul,he]
  simp only [smul_eq_mul,sub_self]

theorem fifty_no_pairings {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    Physics.BipartiteNormalForm.NoPairings r fifty := by
  intro f
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply fifty_dual_no_eigen y hy
  have hi := DFunLike.congr_fun (f.isIntertwining' (1,1,root)) v
  change f (r (1,1,root) v) = fifty.dual (1,1,root) (f v) at hi
  rw [hr root v,map_smul] at hi
  exact hi.symm

theorem selected_no_pairings :
    Physics.BipartiteNormalForm.NoPairings quark fifty ∧
    Physics.BipartiteNormalForm.NoPairings upRight.dual fifty ∧
    Physics.BipartiteNormalForm.NoPairings electronRight.dual fifty :=
  ⟨fifty_no_pairings quark 1 quark_hypercharge (by decide),
    fifty_no_pairings upRight.dual (-4) upLeft_hypercharge (by decide),
    fifty_no_pairings electronRight.dual 6 electronLeft_hypercharge (by decide)⟩

theorem fifty_dual_no_pairings {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    Physics.BipartiteNormalForm.NoPairings r fifty.dual := by
  intro f
  let e := SplitRepresentationProjection.bidualEquiv fifty
  have he := fifty_hom_zero r y hr hy (e.symm.toIntertwiningMap.comp f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply e.symm.toLinearEquiv.injective
  have hz := DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap he) v
  simpa using hz

theorem fifty_dual_hom_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ))
    (f : IntertwiningMap r fifty.dual) : f=0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply fifty_dual_no_eigen y hy
  have hi := DFunLike.congr_fun (f.isIntertwining' (1,1,root)) v
  change f (r (1,1,root) v) = fifty.dual (1,1,root) (f v) at hi
  rw [hr root v,map_smul] at hi
  exact hi.symm

/-- Exact selected multiplicity zero, not merely a dimension bound. -/
theorem fifty_hom_finrank_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    Module.finrank ℂ (IntertwiningMap r fifty) = 0 := by
  have : Subsingleton (IntertwiningMap r fifty) := ⟨fun f g =>
    (fifty_hom_zero r y hr hy f).trans (fifty_hom_zero r y hr hy g).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem fifty_dual_hom_finrank_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (hr : HasHypercharge r y)
    (hy : y ∈ ([-6,-4,-1,1,4,6] : List ℤ)) :
    Module.finrank ℂ (IntertwiningMap r fifty.dual) = 0 := by
  have : Subsingleton (IntertwiningMap r fifty.dual) := ⟨fun f g =>
    (fifty_dual_hom_zero r y hr hy f).trans (fifty_dual_hom_zero r y hr hy g).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end GUT.SU5.ExoticHyperchargeBasis





