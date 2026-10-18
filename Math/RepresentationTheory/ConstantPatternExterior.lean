import Math.RepresentationTheory.PatternExteriorSource

/-! A constant species content is the exterior power of that species. -/
namespace Math.ConstantPatternExterior
set_option autoImplicit false
noncomputable section
open Representation
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (s : S) (n : ℕ)

def forward : (⋀[ℂ]^n (V s)) →ₗ[ℂ] PatternExteriorSource.Source r (fun _ : Fin n => s) :=
  (PatternExteriorSource.projectionLinear r (fun _ : Fin n => s)).comp
    (exteriorPower.map n (LinearMap.single ℂ V s))

def backward : PatternExteriorSource.Source r (fun _ : Fin n => s) →ₗ[ℂ]
    (⋀[ℂ]^n (V s)) :=
  (exteriorPower.map n (LinearMap.proj s)).comp (PatternExteriorSource.Source r _).subtype

theorem forward_pure (v : Fin n → V s) :
    forward r s n (exteriorPower.ιMulti ℂ n v) =
      PatternExteriorSource.pure r (fun _ : Fin n => s) v := by
  simp only [forward, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti]
  exact PatternExteriorSource.projection_pure r _ v

theorem backward_pure (v : Fin n → V s) :
    backward r s n (PatternExteriorSource.pure r (fun _ : Fin n => s) v) =
      exteriorPower.ιMulti ℂ n v := by
  simp [backward, PatternExteriorSource.pure_val, exteriorPower.map_apply_ιMulti,
    Function.comp_def]

theorem backward_forward : (backward r s n).comp (forward r s n) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change backward r s n (forward r s n (exteriorPower.ιMulti ℂ n v)) = _
  rw [forward_pure, backward_pure]
  rfl

theorem forward_backward (x : PatternExteriorSource.Source r (fun _ : Fin n => s)) :
    forward r s n (backward r s n x) = x := by
  obtain ⟨y,rfl⟩ := PatternExteriorSource.onto_surjective r (fun _ : Fin n => s) x
  have he : ((forward r s n).comp (backward r s n)).comp
      (PatternExteriorSource.onto r (fun _ : Fin n => s)).toLinearMap =
      (PatternExteriorSource.onto r (fun _ : Fin n => s)).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change forward r s n (backward r s n (PatternExteriorSource.pure r _ v)) = _
    rw [backward_pure, forward_pure]
    rfl
  exact LinearMap.congr_fun he y

def linearEquiv : (⋀[ℂ]^n (V s)) ≃ₗ[ℂ]
    PatternExteriorSource.Source r (fun _ : Fin n => s) :=
  { forward r s n with
    invFun := backward r s n
    left_inv := fun x => LinearMap.congr_fun (backward_forward r s n) x
    right_inv := forward_backward r s n }

def equiv : Representation.Equiv ((r s).exteriorPower n)
    (PatternExteriorSource.representation r (fun _ : Fin n => s)) where
  toLinearEquiv := linearEquiv r s n
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change forward r s n (((r s).exteriorPower n) g (exteriorPower.ιMulti ℂ n v)) =
      (PatternExteriorSource.representation r _) g (forward r s n (exteriorPower.ιMulti ℂ n v))
    rw [Representation.exteriorPower_apply_ιMulti, forward_pure, forward_pure]
    exact PatternExteriorSource.pure_action r _ g v

end
end Math.ConstantPatternExterior
