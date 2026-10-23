import Physics.FieldTheory.Mass.Spectrum.EquivariantMassIndex
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas

open Math

/-!
# Dirac mass maps in all-left-handed Weyl notation

A linear mass map `M : V -> W` defines a symmetric off-diagonal bilinear
on `F = V x W*`. The negative signed sector is dualized when interpreted as
left-handed fields. The radical is `ker M x annihilator(range M)`.

The dual chiral character of `F` is the antisymmetrization of the signed
character of `V - W`. This distinction matters: it does not identify an
arbitrary signed index with its antisymmetrization.
-/

namespace Physics.DiracWeylConvention

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The symmetric two-component mass coefficient of a Dirac mass map. -/
def massBilinear (M : V →ₗ[ℂ] W) :
    LinearMap.BilinForm ℂ (V × Module.Dual ℂ W) where
  toFun x :=
    { toFun := fun y => y.2 (M x.1) + x.2 (M y.1)
      map_add' := by intros; simp [add_left_comm, add_comm]
      map_smul' := by intros; simp [mul_add] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change y.2 (M (x.1 + z.1)) + (x.2 + z.2) (M y.1) =
      (y.2 (M x.1) + x.2 (M y.1)) + (y.2 (M z.1) + z.2 (M y.1))
    simp only [map_add, LinearMap.add_apply]
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change y.2 (M (c • x.1)) + (c • x.2) (M y.1) =
      c • (y.2 (M x.1) + x.2 (M y.1))
    simp [mul_add]

@[simp]
theorem massBilinear_apply (M : V →ₗ[ℂ] W)
    (x y : V × Module.Dual ℂ W) :
    massBilinear M x y = y.2 (M x.1) + x.2 (M y.1) := rfl

/-- Dirac blocks are symmetric on the full all-left-handed field space. -/
theorem massBilinear_isSymm (M : V →ₗ[ℂ] W) :
    (massBilinear M).IsSymm :=
  ⟨fun _ _ => add_comm _ _⟩

/-- The exact zero-mode subspace of the bilinear coefficient. -/
def radical (M : V →ₗ[ℂ] W) : Submodule ℂ (V × Module.Dual ℂ W) :=
  LinearMap.ker (massBilinear M)

/-- Left-handed zero modes are the unmatched source vectors and target
covectors that vanish on the mass range. -/
theorem mem_radical_iff (M : V →ₗ[ℂ] W) (x : V × Module.Dual ℂ W) :
    x ∈ radical M ↔ M x.1 = 0 ∧ ∀ v, x.2 (M v) = 0 := by
  change massBilinear M x = 0 ↔ _
  constructor
  · intro hx
    constructor
    · apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
      intro phi
      have h := LinearMap.congr_fun hx (0, phi)
      simpa using h
    · intro v
      have h := LinearMap.congr_fun hx (v, 0)
      simpa using h
  · rintro ⟨hx, hphi⟩
    apply LinearMap.ext
    intro y
    simp [hx, hphi]

/-- The radical calculation as an equality of submodules. -/
theorem radical_eq_ker_prod_annihilator (M : V →ₗ[ℂ] W) :
    radical M = (LinearMap.ker M).prod (LinearMap.range M).dualAnnihilator := by
  ext x
  rw [mem_radical_iff]
  simp [Submodule.mem_dualAnnihilator, LinearMap.mem_range]

variable {G : Type*} [Group G]
variable {rhoV : Representation ℂ G V} {rhoW : Representation ℂ G W}

/-- Duality includes every factor of the unbroken group, including residual
Abelian charges when `G` is a gauge-times-residual product. -/
theorem massBilinear_invariant
    (M : Representation.IntertwiningMap rhoV rhoW) (g : G)
    (x y : V × Module.Dual ℂ W) :
    massBilinear M ((rhoV.prod rhoW.dual) g x)
        ((rhoV.prod rhoW.dual) g y) = massBilinear M x y := by
  change y.2 (rhoW g⁻¹ (M (rhoV g x.1))) +
    x.2 (rhoW g⁻¹ (M (rhoV g y.1))) = _
  rw [Representation.IntertwiningMap.isIntertwining rhoV rhoW M,
    Representation.IntertwiningMap.isIntertwining rhoV rhoW M]
  simp

/-- The radical of the Dirac bilinear is invariant under the full unbroken
group action on all-left-handed fields. -/
def radicalSubrepresentation
    (M : Representation.IntertwiningMap rhoV rhoW) :
    Subrepresentation (rhoV.prod rhoW.dual) where
  toSubmodule := radical M
  apply_mem_toSubmodule g x hx := by
    change massBilinear M ((rhoV.prod rhoW.dual) g x) = 0
    apply LinearMap.ext
    intro y
    have hy : (rhoV.prod rhoW.dual) g ((rhoV.prod rhoW.dual) g⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← hy, massBilinear_invariant]
    exact LinearMap.congr_fun hx _

/-- Covectors vanishing on an invariant subspace form an invariant subspace
of the contragredient representation. -/
def annihilatorSubrepresentation (S : Subrepresentation rhoW) :
    Subrepresentation rhoW.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g phi hphi := by
    rw [Submodule.mem_dualAnnihilator] at hphi ⊢
    intro w hw
    exact hphi (rhoW g⁻¹ w) (S.apply_mem_toSubmodule g⁻¹ hw)

theorem mem_rangeAnnihilator_iff
    (M : Representation.IntertwiningMap rhoV rhoW) (phi : Module.Dual ℂ W) :
    phi ∈ (annihilatorSubrepresentation M.range).toSubmodule ↔
      ∀ v, phi (M v) = 0 := by
  simp [annihilatorSubrepresentation, Submodule.mem_dualAnnihilator,
    Representation.IntertwiningMap.range, LinearMap.mem_range]

/-- The coordinate decomposition of the bilinear radical. -/
def radicalLinearEquiv (M : V →ₗ[ℂ] W) :
    radical M ≃ₗ[ℂ] (LinearMap.ker M) × (LinearMap.range M).dualAnnihilator where
  toFun x :=
    (⟨x.val.1, ((mem_radical_iff M x.val).mp x.property).1⟩,
     ⟨x.val.2, (Submodule.mem_dualAnnihilator _).mpr (by
       rintro _ ⟨v, rfl⟩
       exact ((mem_radical_iff M x.val).mp x.property).2 v)⟩)
  invFun x := ⟨(x.1.val, x.2.val), (mem_radical_iff M _).mpr
    ⟨x.1.property, fun v => (Submodule.mem_dualAnnihilator _).mp
      x.2.property (M v) ⟨v, rfl⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The radical decomposition also intertwines the unbroken group actions. -/
def radicalDecompositionEquiv
    (M : Representation.IntertwiningMap rhoV rhoW) :
    Representation.Equiv (radicalSubrepresentation M).toRepresentation
      (M.ker.toRepresentation.prod
        (annihilatorSubrepresentation M.range).toRepresentation) := by
  let e := radicalLinearEquiv M.toLinearMap
  apply Representation.Equiv.mk e
  intro g
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- Restricting covectors that vanish on `P` to a complement `Q` is a linear
equivalence. This uses the canonical dual of the quotient, not a chosen
identification of a representation with its dual. -/
def annihilatorComplementEquiv (P Q : Submodule ℂ W) (h : IsCompl P Q) :
    P.dualAnnihilator ≃ₗ[ℂ] Module.Dual ℂ Q :=
  P.dualQuotEquivDualAnnihilator.symm.trans
    (P.quotientEquivOfIsCompl Q h).symm.dualMap

@[simp]
theorem annihilatorComplementEquiv_apply
    (P Q : Submodule ℂ W) (h : IsCompl P Q)
    (phi : P.dualAnnihilator) (q : Q) :
    annihilatorComplementEquiv P Q h phi q = phi.val q := rfl

/-- The annihilator carries the dual action of any invariant complement. -/
def annihilatorComplementRepresentationEquiv
    (S T : Subrepresentation rhoW) (h : IsCompl S.toSubmodule T.toSubmodule) :
    Representation.Equiv (annihilatorSubrepresentation S).toRepresentation
      T.toRepresentation.dual :=
  .mk (annihilatorComplementEquiv S.toSubmodule T.toSubmodule h) (by
    intro g
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro t
    rfl)

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- The dual chiral character of the all-left-handed field space is the
antisymmetrization of the source-minus-target character. -/
theorem allLeft_dual_character_eq_signed_antisymmetrization (g : G) :
    (rhoV.prod rhoW.dual).character g -
        (rhoV.prod rhoW.dual).dual.character g =
      (rhoV.character g - rhoW.character g) -
        (rhoV.character g⁻¹ - rhoW.character g⁻¹) := by
  rw [Representation.char_dual]
  rw [show (rhoV.prod rhoW.dual).character g =
    rhoV.character g + rhoW.dual.character g from LinearMap.trace_prodMap' _ _,
    show (rhoV.prod rhoW.dual).character g⁻¹ =
    rhoV.character g⁻¹ + rhoW.dual.character g⁻¹ from LinearMap.trace_prodMap' _ _]
  rw [Representation.char_dual, Representation.char_dual, inv_inv]
  ring

section Unitary

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {sigmaE : Representation ℂ G E} {sigmaF : Representation ℂ G F}

open CompactEmbeddingClassification EquivariantMassIndex

/-- The actual left-handed zero-mode character is the kernel character plus
the dual cokernel character, with the cokernel realized orthogonally. -/
theorem radical_character_eq_kernel_add_dual_cokernel
    (M : Representation.IntertwiningMap sigmaE sigmaF)
    (hF : IsUnitaryRepresentation sigmaF) (g : G) :
    (radicalSubrepresentation M).toRepresentation.character g =
      M.ker.toRepresentation.character g +
        (orthogonalSubrepresentation sigmaF hF M.range).toRepresentation.dual.character g := by
  rw [congrFun (Representation.char_iso (radicalDecompositionEquiv M)) g]
  rw [show (M.ker.toRepresentation.prod
      (annihilatorSubrepresentation M.range).toRepresentation).character g =
    M.ker.toRepresentation.character g +
      (annihilatorSubrepresentation M.range).toRepresentation.character g
      from LinearMap.trace_prodMap' _ _]
  congr 1
  exact congrFun (Representation.char_iso
    (annihilatorComplementRepresentationEquiv M.range
      (orthogonalSubrepresentation sigmaF hF M.range)
      M.range.toSubmodule.isCompl_orthogonal)) g

/-- At the level of the massless fields, dual chiral difference equals the
antisymmetrization of the existing signed Dirac index. -/
theorem radical_dual_character_eq_lightIndex_antisymmetrization
    (M : Representation.IntertwiningMap sigmaE sigmaF)
    (hF : IsUnitaryRepresentation sigmaF) (g : G) :
    (radicalSubrepresentation M).toRepresentation.character g -
        (radicalSubrepresentation M).toRepresentation.dual.character g =
      lightIndexCharacter M hF g - lightIndexCharacter M hF g⁻¹ := by
  rw [Representation.char_dual,
    radical_character_eq_kernel_add_dual_cokernel M hF g,
    radical_character_eq_kernel_add_dual_cokernel M hF g⁻¹,
    Representation.char_dual, Representation.char_dual, inv_inv]
  unfold lightIndexCharacter
  ring

/-- The all-left-handed dual chiral character is preserved upon removal of
the states made massive by this Dirac bilinear. -/
theorem radical_dual_character_eq_allLeft_dual_character
    (M : Representation.IntertwiningMap sigmaE sigmaF)
    (hE : IsUnitaryRepresentation sigmaE)
    (hF : IsUnitaryRepresentation sigmaF) (g : G) :
    (radicalSubrepresentation M).toRepresentation.character g -
        (radicalSubrepresentation M).toRepresentation.dual.character g =
      (sigmaE.prod sigmaF.dual).character g -
        (sigmaE.prod sigmaF.dual).dual.character g := by
  rw [radical_dual_character_eq_lightIndex_antisymmetrization M hF,
    lightIndexCharacter_eq_source_sub_target M hE hF,
    lightIndexCharacter_eq_source_sub_target M hE hF]
  exact (allLeft_dual_character_eq_signed_antisymmetrization g).symm

end Unitary

end
end Physics.DiracWeylConvention
