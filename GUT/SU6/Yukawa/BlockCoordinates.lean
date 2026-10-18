import GUT.SU6.Yukawa.LightEquations
import Math.LinearAlgebra.SmallSymmetricRank

open Math

/-! A bijective rearrangement of all actual matter coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6YukawaCoordinates
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6YukawaBasis SU6YukawaWeights
open SU6YukawaLight

abbrev Index := Fin 10 ⊕ ((Fin 5 × Fin 3) ⊕ Fin 2)

def freePair (i : Fin 10) : ExteriorSquareCoordinates.Pair 6 :=
  ![⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(0,3), by decide⟩,
    ⟨(0,4), by decide⟩, ⟨(1,2), by decide⟩, ⟨(1,3), by decide⟩,
    ⟨(1,4), by decide⟩, ⟨(2,3), by decide⟩, ⟨(2,4), by decide⟩,
    ⟨(3,4), by decide⟩] i

def label : Index → Label
  | .inl i => .inl (.inl (freePair i))
  | .inr (.inl (i,j)) => ![exteriorLabel i, dualLabel false i.castSucc,
      dualLabel true i.castSucc] j
  | .inr (.inr j) => ![dualLabel false 5, dualLabel true 5] j

theorem label_bijective : Function.Bijective label := by
  let : DecidableEq Label := inferInstance
  let : Fintype Label := inferInstance
  decide

def indexEquiv : Index ≃ Label := Equiv.ofBijective label label_bijective

def assemble : (Index → ℂ) ≃ₗ[ℂ] SmallSymmetricRank.Coordinates ℂ where
  toFun f := (fun i => f (.inl i), ((fun i j => f (.inr (.inl (i,j)))),
    fun j => f (.inr (.inr j))))
  invFun x := Sum.elim x.1 (Sum.elim (fun p => x.2.1 p.1 p.2) x.2.2)
  left_inv f := by funext i; rcases i with i | (⟨i,j⟩ | j) <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def reindex : (Label → ℂ) ≃ₗ[ℂ] (Index → ℂ) where
  toFun f := f ∘ indexEquiv
  invFun f := f ∘ indexEquiv.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : UV ≃ₗ[ℂ] SmallSymmetricRank.Coordinates ℂ :=
  basis.equivFun.trans (reindex.trans assemble)

theorem coordinate_dual (x : UV) (i : Fin 6) :
    basis.equivFun x (dualLabel false i) = fcoord x i ∧
    basis.equivFun x (dualLabel true i) = gcoord x i := by
  have h0 : (LinearMap.proj (dualLabel false i)).comp basis.equivFun.toLinearMap = fMap i := by
    apply basis.ext
    intro j
    change basis.equivFun (basis j) (dualLabel false i) = fcoord (basis j) i
    rw [Module.Basis.equivFun_self]
    rcases j with (p | j) | j <;>
      simp [basis, Module.Basis.prod_apply, dualLabel, fcoord, dualBasis_coordinates,
        Pi.single_apply, eq_comm]
  have h1 : (LinearMap.proj (dualLabel true i)).comp basis.equivFun.toLinearMap = gMap i := by
    apply basis.ext
    intro j
    change basis.equivFun (basis j) (dualLabel true i) = gcoord (basis j) i
    rw [Module.Basis.equivFun_self]
    rcases j with (p | j) | j <;>
      simp [basis, Module.Basis.prod_apply, dualLabel, gcoord, dualBasis_coordinates,
        Pi.single_apply, eq_comm]
  exact ⟨LinearMap.congr_fun h0 x, LinearMap.congr_fun h1 x⟩

theorem coordinate_exterior (x : UV) (i : Fin 5) :
    basis.equivFun x (exteriorLabel i) = zcoord x i.castSucc := by
  have he : (LinearMap.proj (exteriorLabel i)).comp basis.equivFun.toLinearMap =
      zMap i.castSucc := by
    apply basis.ext
    intro j
    change basis.equivFun (basis j) (exteriorLabel i) = zcoord (basis j) i.castSucc
    rw [Module.Basis.equivFun_self]
    rcases j with (p | j) | j
    · have hp : p = wedgeFive i ↔ p.val.1 = i.castSucc ∧ p.val.2 = 5 := by
        simp [wedgeFive, Subtype.ext_iff, Prod.ext_iff]
      simp only [exteriorLabel, Sum.inl.injEq]
      by_cases h2 : p.val.2 = 5 <;> by_cases h1 : p.val.1 = i.castSucc
      all_goals simp [hp, basis, Module.Basis.prod_apply, zcoord, contract_basis,
        h1, h2, eq_comm]
    · simp [basis, Module.Basis.prod_apply, zcoord, exteriorLabel]
    · simp [basis, Module.Basis.prod_apply, zcoord, exteriorLabel]
  exact LinearMap.congr_fun he x

theorem coordinates_triple (x : UV) (i : Fin 5) :
    (coordinates x).2.1 i = ![zcoord x i.castSucc, fcoord x i.castSucc, gcoord x i.castSucc] := by
  funext j
  fin_cases j
  · exact coordinate_exterior x i
  · exact (coordinate_dual x i.castSucc).1
  · exact (coordinate_dual x i.castSucc).2

theorem coordinates_singlet (x : UV) :
    (coordinates x).2.2 = ![fcoord x 5, gcoord x 5] := by
  funext j
  fin_cases j
  · exact (coordinate_dual x 5).1
  · exact (coordinate_dual x 5).2

theorem kernel_iff (a b u v w : ℂ) (x : UV) :
    coordinates x ∈ (SmallSymmetricRank.blockMap a b u v w).ker ↔
      LightConditions a b u v w x := by
  rw [SmallSymmetricRank.mem_block_kernel]
  simp only [coordinates_triple, coordinates_singlet]
  simp [SmallSymmetricRank.star, SmallSymmetricRank.singlet,
    funext_iff, Fin.forall_fin_succ, LightConditions, mul_comm]

def radicalBlockEquiv (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    (SU6FiveCouplings.mass H a b u v w).radical.toSubmodule ≃ₗ[ℂ]
      (SmallSymmetricRank.blockMap a b u v w).ker where
  toFun x := ⟨coordinates x.val, (kernel_iff a b u v w x.val).mpr
    ((radical_iff H a b u v w x.val).mp x.property)⟩
  invFun x := ⟨coordinates.symm x.val, (radical_iff H a b u v w _).mpr
    ((kernel_iff a b u v w _).mp (by simp only [LinearEquiv.apply_symm_apply]; exact x.property))⟩
  left_inv x := Subtype.ext (coordinates.symm_apply_apply x.val)
  right_inv x := Subtype.ext (coordinates.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (coordinates.map_add x.val y.val)
  map_smul' c x := Subtype.ext (coordinates.map_smul c x.val)

theorem radical_finrank (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Module.finrank ℂ (SU6FiveCouplings.mass H a b u v w).radical.toSubmodule =
      10 + 5 * (3 - (if a = 0 ∧ b = 0 then 0 else 2)) +
        (2 - (if u = 0 ∧ v = 0 ∧ w = 0 then 0 else if u * w - v * v = 0 then 1 else 2)) :=
  (radicalBlockEquiv H a b u v w).finrank_eq.trans (SmallSymmetricRank.block_nullity a b u v w)

theorem radical_finrank_cases (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Module.finrank ℂ (SU6FiveCouplings.mass H a b u v w).radical.toSubmodule ∈
      ({15, 16, 17, 25, 26, 27} : Finset ℕ) := by
  rw [(radicalBlockEquiv H a b u v w).finrank_eq]
  exact SmallSymmetricRank.block_nullity_cases a b u v w

theorem all_yukawa_dimensions (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    Module.finrank ℂ (generatedMass H Y).radical.toSubmodule ∈
      ({15, 16, 17, 25, 26, 27} : Finset ℕ) := by
  obtain ⟨c, hc, _⟩ := all_yukawas H Y
  rw [hc]
  exact radical_finrank_cases H _ _ _ _ _

theorem all_nonzero_dimension_sixteen (H : Type*) [CommGroup H] :
    Module.finrank ℂ (SU6FiveCouplings.mass H 1 1 1 1 1).radical.toSubmodule = 16 := by
  rw [(radicalBlockEquiv H 1 1 1 1 1).finrank_eq]
  exact SmallSymmetricRank.nonzero_coefficients_rank_drop

end
end GUT.SU6YukawaCoordinates
