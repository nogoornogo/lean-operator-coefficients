import GUT.SU6.Boundary.BaryonAction

/-! Scalar-dressed boundary contractions. The conjugate of a right-handed
Dirac component is a dual field. All identities are tensor-natural; no
boundary coefficient or brane mass value is assumed nonzero. -/
namespace GUT.SU6BoundaryInteractions
set_option autoImplicit false
noncomputable section
open Math Physics SU6BoundaryBaryon SU6BoundaryCube
open scoped TensorProduct

abbrev singlet : Vector →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ Physics.SMEpsilonTensor.Weak ℂ).comp
    ((LinearMap.snd ℂ Physics.SMEpsilonTensor.Color _).comp StandardSMGroup.splitEquiv.toLinearMap)

def vev (a : ℂ) : Vector := StandardSMGroup.splitEquiv.symm (0,(0,a))

theorem vev_fixed (z : Circle) (a : ℂ) : defining z (vev a) = vev a := by
  apply StandardSMGroup.splitEquiv.injective
  rw [defining_action]
  simp [vev,splitAction]

theorem singlet_fixed (z : Circle) (v : Vector) : singlet (defining z v) = singlet v :=
  congrArg (fun x : StandardSMExterior.Six => x.2.2) (defining_action z v)

/-- Wedge a supplied brane scalar into a fifteen. -/
def join (a : ℂ) : Square →ₗ[ℂ] Cube :=
  ExteriorCubeHook.multiply.comp (TensorProduct.mk ℂ Vector Square (vev a))

theorem join_covariant (z : Circle) (a : ℂ) (x : Square) :
    join a (defining.exteriorPower 2 z x) = defining.exteriorPower 3 z (join a x) := by
  change ExteriorCubeHook.multiply (vev a ⊗ₜ[ℂ] exteriorPower.map 2 (defining z) x) = _
  rw [← vev_fixed z a]
  exact ExteriorCubeHook.multiply_natural (defining z) _ _

/-- Contract the conjugate brane scalar out of a twenty. -/
def strip : Cube →ₗ[ℂ] Square :=
  ((TensorProduct.lid ℂ Square).toLinearMap.comp
    (TensorProduct.map singlet (LinearMap.id : Square →ₗ[ℂ] Square))).comp ExteriorCubeHook.coproduct

@[simp] theorem strip_cube (a b c : Vector) :
    strip (ExteriorCubeHook.cube a b c) =
      singlet a • TensorSquareQuotients.wedge (b ⊗ₜ[ℂ] c) -
      singlet b • TensorSquareQuotients.wedge (a ⊗ₜ[ℂ] c) +
      singlet c • TensorSquareQuotients.wedge (a ⊗ₜ[ℂ] b) := by
  simp [strip,ExteriorCubeHook.coproduct_pure,TensorProduct.map_tmul]

@[simp] theorem singlet_vev (a : ℂ) : singlet (vev a) = a := by
  change (StandardSMGroup.splitEquiv (StandardSMGroup.splitEquiv.symm (0,(0,a)))).2.2 = a
  rw [StandardSMGroup.splitEquiv.apply_symm_apply]

/-- Non-vacuity: on scalar-free wedges, the UV inclusion has this IR retraction. -/
theorem strip_join_pure (a b : Vector) (ha : singlet a = 0) (hb : singlet b = 0) :
    strip (join 1 (TensorSquareQuotients.wedge (a ⊗ₜ[ℂ] b))) =
      TensorSquareQuotients.wedge (a ⊗ₜ[ℂ] b) := by
  change strip (ExteriorCubeHook.multiply (vev 1 ⊗ₜ[ℂ] _)) = _
  rw [ExteriorCubeHook.multiply_pure,strip_cube,singlet_vev,ha,hb]
  simp

theorem strip_covariant (z : Circle) (x : Cube) :
    strip (defining.exteriorPower 3 z x) = defining.exteriorPower 2 z (strip x) := by
  let t := (TensorProduct.lid ℂ Square).toLinearMap.comp
    (TensorProduct.map singlet (LinearMap.id : Square →ₗ[ℂ] Square))
  have ht : t.comp (TensorProduct.map (defining z) (defining.exteriorPower 2 z)) =
      (defining.exteriorPower 2 z).comp t := by
    apply TensorProduct.ext'; intro v w
    change singlet (defining z v) • defining.exteriorPower 2 z w =
      defining.exteriorPower 2 z (singlet v • w)
    rw [singlet_fixed,map_smul]
  change t (ExteriorCubeHook.coproduct (exteriorPower.map 3 (defining z) x)) = _
  rw [ExteriorCubeHook.coproduct_natural]
  exact LinearMap.congr_fun ht (ExteriorCubeHook.coproduct x)

/-- A common proof for all projected Dirac pairings; the first field is dual. -/
theorem pairing_invariant {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (r : Representation ℂ Circle V) (s : Representation ℂ Circle W)
    (t : V →ₗ[ℂ] W) (ht : ∀ z x, t (r z x) = s z (t x))
    (z : Circle) (f : Module.Dual ℂ W) (x : V) :
    s.dual z f (t (r z x)) = f (t x) := by
  change f (s z⁻¹ (t (r z x))) = _
  rw [ht,Representation.inv_self_apply]

theorem uv_20_15_invariant (z : Circle) (a : ℂ) (f : Module.Dual ℂ Cube) (x : Square) :
    (defining.exteriorPower 3).dual z f (join a (defining.exteriorPower 2 z x)) = f (join a x) :=
  pairing_invariant _ _ _ (fun z x => join_covariant z a x) z f x

theorem ir_15_20_invariant (z : Circle) (f : Module.Dual ℂ Square) (x : Cube) :
    (defining.exteriorPower 2).dual z f (strip (defining.exteriorPower 3 z x)) = f (strip x) :=
  pairing_invariant _ _ _ strip_covariant z f x

/-- Strip the scalar from a fifteen, obtaining the two six-component IR pairings. -/
def stripSquareAlternating : Vector [⋀^Fin 2]→ₗ[ℂ] Vector where
  toFun v := singlet (v 0) • v 1 - singlet (v 1) • v 0
  map_update_add' v i a b := by
    fin_cases i <;> simp [Function.update,add_smul,smul_add] <;> module
  map_update_smul' v i c a := by
    fin_cases i <;> simp [Function.update,smul_smul] <;> module
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij; rw [hij]; exact sub_self _
    · change v 1 = v 0 at hij; rw [hij]; exact sub_self _
    · exact (hne rfl).elim

def stripSquare : Square →ₗ[ℂ] Vector := exteriorPower.alternatingMapLinearEquiv stripSquareAlternating

@[simp] theorem stripSquare_wedge (a b : Vector) :
    stripSquare (exteriorPower.ιMulti ℂ 2 ![a,b]) = singlet a • b - singlet b • a :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem stripSquare_vev (v : Vector) (hv : singlet v = 0) :
    stripSquare (exteriorPower.ιMulti ℂ 2 ![vev 1,v]) = v := by
  rw [stripSquare_wedge,singlet_vev,hv]
  simp

theorem stripSquare_covariant (z : Circle) (x : Square) :
    stripSquare (defining.exteriorPower 2 z x) = defining z (stripSquare x) := by
  have he : stripSquare.comp (defining.exteriorPower 2 z) = (defining z).comp stripSquare := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext; intro v
    change stripSquare (exteriorPower.map 2 (defining z) (exteriorPower.ιMulti ℂ 2 v)) = _
    rw [exteriorPower.map_apply_ιMulti]
    simp only [stripSquare,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.compAlternatingMap_apply,LinearMap.comp_apply]
    change singlet (defining z (v 0)) • defining z (v 1) -
      singlet (defining z (v 1)) • defining z (v 0) = defining z (singlet (v 0) • v 1 - singlet (v 1) • v 0)
    rw [singlet_fixed,singlet_fixed,map_sub,map_smul,map_smul]
  exact LinearMap.congr_fun he x

theorem ir_6_15_invariant (z : Circle) (f : Module.Dual ℂ Vector) (x : Square) :
    defining.dual z f (stripSquare (defining.exteriorPower 2 z x)) = f (stripSquare x) :=
  pairing_invariant _ _ _ stripSquare_covariant z f x

theorem ir_1_6_invariant (z : Circle) (f : Module.Dual ℂ ℂ) (v : Vector) :
    (Representation.trivial ℂ Circle ℂ).dual z f (singlet (defining z v)) = f (singlet v) := by
  rw [singlet_fixed]
  rfl

/-- Source-convention control: Φ ψ20 χ15 has degrees 1-3+2, not 1+3+2. -/
theorem uv_central_balance (z : Circle) : z * z^(-3 : ℤ) * z^2 = 1 := by group

theorem wrong_conjugation_charge : ((1+3+2 : ℤ) : ZMod 4) ≠ 0 := by decide +kernel

theorem wrong_conjugation_not_invariant :
    ¬ ∀ g : CyclicCharge.Group 4,
      ZMod.stdAddChar (((1+3+2 : ℤ) : ZMod 4)*Multiplicative.toAdd g) = 1 := by
  intro h
  exact wrong_conjugation_charge ((CyclicCharge.neutral_iff _).mp h)

end
end GUT.SU6BoundaryInteractions
