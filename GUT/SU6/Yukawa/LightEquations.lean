import GUT.SU6.Yukawa.VacuumImage

open Physics

open Math

/-! Exact light-field equations for the exhaustive generated mass family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6YukawaLight
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6FiveCouplings
open SU6YukawaBasis SU6YukawaWeights

theorem contract_basis (p : ExteriorSquareCoordinates.Pair 6) :
    contract (exteriorCoordinates (exteriorBasis p)) =
      if p.val.2 = 5 then Pi.single p.val.1 1 else 0 := by
  rw [exteriorBasis_coordinates, ExteriorSquareCoordinates.basis_apply, contract_wedge]
  have hn : p.val.1 ≠ 5 := by
    intro h
    have := p.property
    have := p.val.2.isLt
    simp only [h, Fin.lt_def] at *
    omega
  by_cases h : p.val.2 = 5
  · simp [h, Ne.symm hn]
  · simp [h, Ne.symm hn, Ne.symm h]

theorem contract_last (z : ConcreteSU6Representations.exteriorTwo.V) :
    contract (exteriorCoordinates z) 5 = 0 := by
  have he : (LinearMap.proj 5).comp
      (contract.comp exteriorCoordinates.toLinearEquiv.toLinearMap) =
      (0 : ConcreteSU6Representations.exteriorTwo.V →ₗ[ℂ] ℂ) := by
    apply exteriorBasis.ext
    intro p
    change contract (exteriorCoordinates (exteriorBasis p)) 5 = 0
    rw [contract_basis]
    split_ifs with h
    · have hn : p.val.1 ≠ 5 := by
        intro he
        have hp := p.property
        simp [he, h] at hp
      simp [Ne.symm hn]
    · rfl
  exact LinearMap.congr_fun he z

theorem dual_single (f : ConcreteSU6Representations.antifundamental.V) (i : Fin 6) :
    dualCoordinates f (Pi.single i 1) = (Pi.basisFun ℂ (Fin 6)).dualBasis.repr
      (dualCoordinates f) i := by
  simp

def fcoord (x : UV) (i : Fin 6) : ℂ := dualCoordinates x.1.2 (Pi.single i 1)
def gcoord (x : UV) (i : Fin 6) : ℂ := dualCoordinates x.2 (Pi.single i 1)
def zcoord (x : UV) (i : Fin 6) : ℂ := contract (exteriorCoordinates x.1.1) i

theorem single_five : (Pi.single 5 1 : Six) = sixth := by
  funext i
  fin_cases i <;> norm_num [Pi.single_apply, sixth, Fin.ext_iff]

theorem singlet_f (x : UV) : singletCoordinate x.1.2 = fcoord x 5 := by
  rw [fcoord, single_five]
  rfl

theorem singlet_g (x : UV) : singletCoordinate x.2 = gcoord x 5 := by
  rw [gcoord, single_five]
  rfl

theorem row_exterior (H : Type*) [CommGroup H] (a b u v w : ℂ)
    (x : UV) (p : ExteriorSquareCoordinates.Pair 6) :
    (mass H a b u v w).form x (basis (.inl (.inl p))) =
      if p.val.2 = 5 then a * fcoord x p.val.1 + b * gcoord x p.val.1 else 0 := by
  rw [SU6FiveCouplings.mass_formula]
  simp only [basis, Module.Basis.prod_apply]
  simp [fivePair, singletCoordinate, contract_basis, fcoord, gcoord]
  split_ifs <;> simp

theorem row_first (H : Type*) [CommGroup H] (a b u v w : ℂ) (x : UV) (i : Fin 6) :
    (mass H a b u v w).form x (basis (dualLabel false i)) =
      a * zcoord x i + if i = 5 then u * fcoord x 5 + v * gcoord x 5 else 0 := by
  rw [SU6YukawaImage.basis_probeA, SU6FiveCouplings.mass_formula]
  simp only [probeA, fivePair, singletCoordinate]
  simp [dualProbe_apply, zcoord, fcoord, gcoord, single_five, sixth]
  fin_cases i <;> simp [Fin.ext_iff, add_assoc]

theorem row_second (H : Type*) [CommGroup H] (a b u v w : ℂ) (x : UV) (i : Fin 6) :
    (mass H a b u v w).form x (basis (dualLabel true i)) =
      b * zcoord x i + if i = 5 then v * fcoord x 5 + w * gcoord x 5 else 0 := by
  rw [SU6YukawaImage.basis_probeB, SU6FiveCouplings.mass_formula]
  simp only [probeB, fivePair, singletCoordinate]
  simp [dualProbe_apply, zcoord, fcoord, gcoord, single_five, sixth]
  fin_cases i <;> simp [Fin.ext_iff, add_assoc]

def LightConditions (a b u v w : ℂ) (x : UV) : Prop :=
  (∀ i : Fin 5, a * fcoord x i.castSucc + b * gcoord x i.castSucc = 0 ∧
    a * zcoord x i.castSucc = 0 ∧ b * zcoord x i.castSucc = 0) ∧
  u * fcoord x 5 + v * gcoord x 5 = 0 ∧ v * fcoord x 5 + w * gcoord x 5 = 0

theorem vanishes_iff (B : LinearMap.BilinForm ℂ UV) (a b u v w : ℂ)
    (h0 : ∀ x p, B x (basis (.inl (.inl p))) =
      if p.val.2 = 5 then a * fcoord x p.val.1 + b * gcoord x p.val.1 else 0)
    (h1 : ∀ x i, B x (basis (dualLabel false i)) =
      a * zcoord x i + if i = 5 then u * fcoord x 5 + v * gcoord x 5 else 0)
    (h2 : ∀ x i, B x (basis (dualLabel true i)) =
      b * zcoord x i + if i = 5 then v * fcoord x 5 + w * gcoord x 5 else 0)
    (x : UV) : (∀ y, B x y = 0) ↔ LightConditions a b u v w x := by
  constructor
  · intro hx
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have hi : i.castSucc ≠ (5 : Fin 6) := by
        intro h
        have := congrArg Fin.val h
        have := i.isLt
        simp at *
        omega
      have he := hx (basis (exteriorLabel i))
      have hf := hx (basis (dualLabel false i.castSucc))
      have hg := hx (basis (dualLabel true i.castSucc))
      rw [exteriorLabel, h0] at he
      simp only [wedgeFive, ite_true] at he
      rw [h1] at hf
      rw [h2] at hg
      exact ⟨he, by simpa [hi] using hf, by simpa [hi] using hg⟩
    · have h := hx (basis (dualLabel false 5))
      rw [h1] at h
      simpa [zcoord, contract_last] using h
    · have h := hx (basis (dualLabel true 5))
      rw [h2] at h
      simpa [zcoord, contract_last] using h
  · intro hx
    have he : B x = 0 := by
      apply basis.ext
      intro j
      change B x (basis j) = 0
      rcases j with (p | i) | i
      · rw [h0]
        split_ifs with hp
        · let i : Fin 5 := ⟨p.val.1.val, by
            have := p.property
            simp only [hp, Fin.lt_def] at this
            exact this⟩
          exact (hx.1 i).1
        · rfl
      · change B x (basis (dualLabel false i)) = 0
        rw [h1]
        by_cases hi : i = 5
        · subst i
          simpa [zcoord, contract_last] using hx.2.1
        · have hb : i.val < 5 := by
            have := i.isLt
            have hn : i.val ≠ 5 := fun h => hi (Fin.ext h)
            omega
          simpa [hi] using (hx.1 ⟨i.val, hb⟩).2.1
      · change B x (basis (dualLabel true i)) = 0
        rw [h2]
        by_cases hi : i = 5
        · subst i
          simpa [zcoord, contract_last] using hx.2.2
        · have hb : i.val < 5 := by
            have := i.isLt
            have hn : i.val ≠ 5 := fun h => hi (Fin.ext h)
            omega
          simpa [hi] using (hx.1 ⟨i.val, hb⟩).2.2
    intro y
    exact LinearMap.congr_fun he y

theorem radical_iff (H : Type*) [CommGroup H] (a b u v w : ℂ) (x : UV) :
    x ∈ (mass H a b u v w).radical.toSubmodule ↔ LightConditions a b u v w x := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical]
  exact vanishes_iff _ a b u v w (row_exterior H a b u v w)
    (row_first H a b u v w) (row_second H a b u v w) x

abbrev Equations := (Fin 5 → Fin 3 → ℂ) × (Fin 2 → ℂ)

def fMap (i : Fin 6) : UV →ₗ[ℂ] ℂ where
  toFun x := fcoord x i
  map_add' x y := by simp only [fcoord, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  map_smul' c x := by
    simp only [fcoord, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

def gMap (i : Fin 6) : UV →ₗ[ℂ] ℂ where
  toFun x := gcoord x i
  map_add' x y := by simp only [gcoord, Prod.snd_add, map_add, LinearMap.add_apply]
  map_smul' c x := by
    simp only [gcoord, Prod.smul_snd, map_smul, LinearMap.smul_apply, RingHom.id_apply]

def zMap (i : Fin 6) : UV →ₗ[ℂ] ℂ where
  toFun x := zcoord x i
  map_add' x y := by simp only [zcoord, Prod.fst_add, map_add, Pi.add_apply]
  map_smul' c x := by
    simp only [zcoord, Prod.smul_fst, map_smul, Pi.smul_apply, RingHom.id_apply]

def constraints (a b u v w : ℂ) : UV →ₗ[ℂ] Equations :=
  (LinearMap.pi fun i : Fin 5 => LinearMap.pi
    ![a • fMap i.castSucc + b • gMap i.castSucc, a • zMap i.castSucc, b • zMap i.castSucc]).prod
  (LinearMap.pi ![u • fMap 5 + v • gMap 5, v • fMap 5 + w • gMap 5])

theorem constraints_apply (a b u v w : ℂ) (x : UV) :
    constraints a b u v w x = ((fun i : Fin 5 =>
      ![a * fcoord x i.castSucc + b * gcoord x i.castSucc,
        a * zcoord x i.castSucc, b * zcoord x i.castSucc]),
      ![u * fcoord x 5 + v * gcoord x 5, v * fcoord x 5 + w * gcoord x 5]) := by
  apply Prod.ext
  · funext i j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl

theorem constraints_ker (a b u v w : ℂ) (x : UV) :
    x ∈ (constraints a b u v w).ker ↔ LightConditions a b u v w x := by
  rw [LinearMap.mem_ker, constraints_apply]
  simp only [Prod.mk_eq_zero, funext_iff, Pi.zero_apply]
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true, LightConditions]

theorem radical_eq_kernel (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    (mass H a b u v w).radical.toSubmodule = (constraints a b u v w).ker := by
  ext x
  rw [radical_iff, constraints_ker]

def radicalKernelEquiv (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    (mass H a b u v w).radical.toSubmodule ≃ₗ[ℂ] (constraints a b u v w).ker :=
  LinearEquiv.ofEq _ _ (radical_eq_kernel H a b u v w)

def generatedMass (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :=
  WeylYukawaMass.atVacuumOn (InvariantWeylMass.SymmetricMass.zero uvRho) Y
    (StandardSMGroup.withResidual H) (StandardSMUVYukawa.vacuum H)
    (StandardSMUVYukawa.vacuum_fixed H)

theorem generatedMass_form (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    (generatedMass H Y).form = Y.toLinearMap (StandardSMUVYukawa.vacuum H) :=
  ProjectedYukawa.zeroBare_form Y (StandardSMGroup.withResidual H)
    (StandardSMUVYukawa.vacuum H) (StandardSMUVYukawa.vacuum_fixed H)

theorem all_yukawas (H : Type*) [CommGroup H]
    (Y : WeylYukawaMass.EquivariantYukawa StandardSMUVYukawa.scalar.rho uvRho) :
    ∃ c : Fin 5 → ℂ,
      generatedMass H Y = mass H (c 0) (c 1) (c 2) (c 3) (c 4) ∧
      ∀ x, x ∈ (generatedMass H Y).radical.toSubmodule ↔
        LightConditions (c 0) (c 1) (c 2) (c 3) (c 4) x := by
  obtain ⟨c, hc⟩ := SU6YukawaImage.evaluation_mem_range H Y
  have he : generatedMass H Y = mass H (c 0) (c 1) (c 2) (c 3) (c 4) := by
    apply InvariantWeylMass.SymmetricMass.ext
    rw [generatedMass_form]
    exact hc.symm
  exact ⟨c, he, fun x => by rw [he]; exact radical_iff H _ _ _ _ _ x⟩

theorem untouched_light (H : Type*) [CommGroup H] (a b u v w : ℂ)
    (p : ExteriorSquareCoordinates.Pair 6) (hp : p.val.2 ≠ 5) :
    basis (.inl (.inl p)) ∈ (mass H a b u v w).radical.toSubmodule := by
  rw [InvariantWeylMass.SymmetricMass.mem_radical]
  intro y
  rw [(mass H a b u v w).symmetric.eq, row_exterior]
  simp [hp]

def pureSinglet (s t : ℂ) : UV := ((0, s • dualProbe 5), t • dualProbe 5)

theorem pureSinglet_conditions (a b u v w s t : ℂ) :
    LightConditions a b u v w (pureSinglet s t) ↔
      u * s + v * t = 0 ∧ v * s + w * t = 0 := by
  unfold LightConditions
  have hz : ∀ i : Fin 5, fcoord (pureSinglet s t) i.castSucc = 0 ∧
      gcoord (pureSinglet s t) i.castSucc = 0 := by
    intro i
    have hi : (5 : Fin 6) ≠ i.castSucc := by
      intro h
      have := congrArg Fin.val h
      have := i.isLt
      simp at *
      omega
    simp [fcoord, gcoord, pureSinglet, dualProbe_apply, hi]
  have hc : ∀ i : Fin 5,
      a * fcoord (pureSinglet s t) i.castSucc + b * gcoord (pureSinglet s t) i.castSucc = 0 ∧
      a * zcoord (pureSinglet s t) i.castSucc = 0 ∧
      b * zcoord (pureSinglet s t) i.castSucc = 0 := by
    intro i
    rw [(hz i).1, (hz i).2]
    simp [zcoord, pureSinglet]
  simp only [hc, true_and]
  simp [pureSinglet, fcoord, gcoord, dualProbe_apply]

theorem pureSinglet_light_iff (H : Type*) [CommGroup H] (a b u v w s t : ℂ) :
    pureSinglet s t ∈ (mass H a b u v w).radical.toSubmodule ↔
      u * s + v * t = 0 ∧ v * s + w * t = 0 := by
  rw [radical_iff, pureSinglet_conditions]

theorem nonzero_couplings_light_singlet (H : Type*) [CommGroup H] :
    pureSinglet 1 (-1) ≠ 0 ∧
      pureSinglet 1 (-1) ∈ (mass H 1 1 1 1 1).radical.toSubmodule := by
  constructor
  · intro h
    have he := congrArg (fun x => fcoord x 5) h
    norm_num [fcoord, pureSinglet, dualProbe_apply] at he
  · rw [pureSinglet_light_iff]
    norm_num

end
end GUT.SU6YukawaLight
