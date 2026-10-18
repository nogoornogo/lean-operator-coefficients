import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Embed the first summand through specified linear coordinates. -/
namespace Math.FirstSummandEmbedding
set_option autoImplicit false
noncomputable section
variable {G A B C D E F L : Type*} [Group G]
variable [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
variable [AddCommMonoid C] [Module ℂ C] [AddCommMonoid D] [Module ℂ D]
variable [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
variable [AddCommMonoid L] [Module ℂ L]

def embedding (e : A ≃ₗ[ℂ] B) (x : B) : (A × C) × E := ((e.symm x, 0), 0)

def linear (e : A ≃ₗ[ℂ] B) : B →ₗ[ℂ] (A × C) × E where
  toFun := embedding e
  map_add' x y := by simp [embedding, map_add]
  map_smul' z x := by simp [embedding, map_smul]

@[simp] theorem linear_apply (e : A ≃ₗ[ℂ] B) (x : B) :
    linear (C := C) (E := E) e x = embedding e x := rfl

theorem scaled_action (e : A ≃ₗ[ℂ] B)
    (f : A →ₗ[ℂ] A) (g : C →ₗ[ℂ] C) (h : E →ₗ[ℂ] E) (b : B →ₗ[ℂ] B)
    (he : ∀ x, e (f (e.symm x)) = b x) (r s t : ℂ) (x : B) :
    (f.prodMap g).prodMap h
      ((r • (embedding (C := C) (E := E) e x).1.1, s • (embedding (C := C) (E := E) e x).1.2), t • (embedding (C := C) (E := E) e x).2) =
      embedding (C := C) (E := E) e (r • b x) := by
  apply Prod.ext
  · apply Prod.ext
    · change f (r • e.symm x) = e.symm (r • b x)
      apply e.injective
      rw [map_smul, map_smul, he, e.apply_symm_apply]
    · simp [embedding]
  · simp [embedding]

theorem action (e : A ≃ₗ[ℂ] B)
    (f : A →ₗ[ℂ] A) (g : C →ₗ[ℂ] C) (h : E →ₗ[ℂ] E) (b : B →ₗ[ℂ] B)
    (he : ∀ x, e (f (e.symm x)) = b x) (x : B) :
    (f.prodMap g).prodMap h (embedding e x) = embedding e (b x) := by
  simpa only [one_smul, Prod.eta] using scaled_action e f g h b he 1 1 1 x

theorem decomposed
    {rho : Representation ℂ G A} {sigma : Representation ℂ G B}
    {tau : Representation ℂ G C} {upsilon : Representation ℂ G D}
    {gamma : Representation ℂ G E} {delta : Representation ℂ G F}
    {lambda : Representation ℂ G L}
    (e : Representation.Equiv rho sigma) (f : Representation.Equiv tau upsilon)
    (g : Representation.Equiv gamma delta)
    (r : Representation.Equiv (sigma.prod upsilon) lambda) (x : B) :
    SplitRepresentationProjection.prodEquiv
      ((SplitRepresentationProjection.prodEquiv e f).trans r) g
      (embedding (C := C) (E := E) e.toLinearEquiv x) = (r (x, (0 : D)), (0 : F)) := by
  rw [SplitRepresentationProjection.prodEquiv_apply, Representation.Equiv.trans_apply,
    SplitRepresentationProjection.prodEquiv_apply]
  simp only [embedding, map_zero]
  exact congrArg (fun y => (r (y, (0 : D)), (0 : F)))
    (e.toLinearEquiv.apply_symm_apply x)
end
end Math.FirstSummandEmbedding
