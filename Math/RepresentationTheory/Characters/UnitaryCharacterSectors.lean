import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity
import Math.RepresentationTheory.Characters.AbelianCharge
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Full character sectors of finite-dimensional unitary Abelian actions

No topology or finiteness is imposed on the group. TauCeti supplies a joint
eigenvector; unitarity puts its character on Circle. Orthogonal complements
then prove that the full character subspaces span the entire representation.
-/

set_option autoImplicit false

namespace Math.UnitaryCharacterSectors

noncomputable section

variable {H E : Type*} [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ H E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)

include hu in
theorem exists_character_eigenvector [Nontrivial E] :
    ∃ (chi : H →* Circle) (v : E), v ≠ 0 ∧ ∀ h, rho h v = (chi h : ℂ) • v := by
  obtain ⟨chi, v, hv, he⟩ :=
    TauCeti.exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed rho
      (fun g h _ => (Commute.all g h).map rho)
  have hn (h : H) : ‖(chi h : ℂ)‖ = 1 := by
    have hs : ‖rho h v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ E _ _ _ (rho h v),
        @norm_sq_eq_re_inner ℂ E _ _ _ v, hu h v v]
    rw [he h, norm_smul, mul_pow] at hs
    have hn0 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    have hs' : ‖(chi h : ℂ)‖ ^ 2 = 1 := by
      apply mul_right_cancel₀ hn0
      simpa using hs
    nlinarith [norm_nonneg (chi h : ℂ)]
  let c : H →* Circle :=
    { toFun := fun h => ⟨chi h, mem_sphere_zero_iff_norm.mpr (hn h)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h k => Subtype.ext (by
        change (chi (h * k) : ℂ) = (chi h : ℂ) * (chi k : ℂ)
        simp) }
  exact ⟨c, v, hv, he⟩

omit [FiniteDimensional ℂ E] in
def sector (chi : H →* Circle) : Subrepresentation rho where
  toSubmodule :=
    { carrier := {v | ∀ h, rho h v = (chi h : ℂ) • v}
      zero_mem' := by simp
      add_mem' := by intro v w hv hw h; simp [hv h, hw h, smul_add]
      smul_mem' := by intro z v hv h; simp [hv h, smul_comm z] }
  apply_mem_toSubmodule g {v} hv h := by
    rw [hv g, map_smul, hv h, smul_comm]

omit [FiniteDimensional ℂ E] in
@[simp] theorem mem_sector (chi : H →* Circle) (v : E) :
    v ∈ sector rho chi ↔ ∀ h, rho h v = (chi h : ℂ) • v := Iff.rfl

omit [FiniteDimensional ℂ E] in
include hu in
theorem distinct_sectors_orthogonal (chi psi : H →* Circle) (hne : chi ≠ psi)
    (v w : E) (hv : v ∈ sector rho chi) (hw : w ∈ sector rho psi) :
    inner ℂ v w = 0 := by
  by_contra hn
  apply hne
  apply MonoidHom.ext
  intro h
  have he := hu h v w
  rw [hv h, hw h, inner_smul_left, inner_smul_right] at he
  have hc : (starRingEnd ℂ) (chi h : ℂ) * (psi h : ℂ) = 1 := by
    apply mul_right_cancel₀ hn
    simpa only [mul_assoc, one_mul] using he
  have hc' : (chi h)⁻¹ * psi h = 1 := by
    apply Subtype.ext
    simpa only [Circle.coe_mul, Circle.coe_one, Circle.coe_inv_eq_conj] using hc
  exact inv_mul_eq_one.mp hc'

include hu in
theorem iSup_sector_eq_top : (⨆ chi, (sector rho chi).toSubmodule) = ⊤ := by
  let P : Subrepresentation rho :=
    { toSubmodule := ⨆ chi, (sector rho chi).toSubmodule
      apply_mem_toSubmodule g {v} hv := by
        refine Submodule.iSup_induction _
          (motive := fun x => rho g x ∈ ⨆ chi, (sector rho chi).toSubmodule) hv ?_ ?_ ?_
        · intro i v hv
          exact Submodule.mem_iSup_of_mem i ((sector rho i).apply_mem_toSubmodule g hv)
        · simp
        · intro x y hx hy
          simpa using Submodule.add_mem (⨆ chi, (sector rho chi).toSubmodule) hx hy
        }
  let Q := UnitaryMultiplicity.orthogonalSubrepresentation rho hu P
  by_contra hp
  have hq : Q.toSubmodule ≠ ⊥ := by
    intro hq
    have hc := (UnitaryMultiplicity.isCompl_orthogonalSubrepresentation rho hu P).sup_eq_top
    have hq' : Q = ⊥ := Subrepresentation.toSubmodule_injective hq
    change P ⊔ Q = ⊤ at hc
    rw [hq', sup_bot_eq] at hc
    exact hp (congrArg Subrepresentation.toSubmodule hc)
  let : Nontrivial Q.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hq
  have huq : UnitaryMultiplicity.IsUnitaryRepresentation Q.toRepresentation :=
    fun h v w => hu h v w
  obtain ⟨chi, v, hv, he⟩ := exists_character_eigenvector Q.toRepresentation huq
  have hvp : (v : E) ∈ P := by
    apply (le_iSup (fun chi => (sector rho chi).toSubmodule) chi)
    intro h
    exact congrArg Subtype.val (he h)
  have hvq : (v : E) ∈ P.toSubmoduleᗮ := v.property
  rw [Submodule.mem_orthogonal] at hvq
  have hv0 : inner ℂ (v : E) (v : E) = 0 := hvq (v : E) hvp
  exact hv (Subtype.ext ((inner_self_eq_zero (𝕜 := ℂ)).mp hv0))

omit [FiniteDimensional ℂ E] in
theorem eigenvector_sector_nonzero (chi : H →* Circle) (v : E)
    (hv : v ≠ 0) (he : ∀ h, rho h v = (chi h : ℂ) • v) :
    (sector rho chi).toSubmodule ≠ ⊥ := by
  intro hz
  have hm : v ∈ (sector rho chi).toSubmodule := he
  rw [hz] at hm
  exact hv hm

end

end Math.UnitaryCharacterSectors
