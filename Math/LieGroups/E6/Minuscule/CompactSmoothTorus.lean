import Math.LieGroups.E6.Minuscule.CompactTorus
import Math.LieGroups.E6.Minuscule.TorusCoordinates
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth structure on the torus and smooth torus inclusion

The torus `Torus.Point = Fin 6 → Circle` is given a charted space structure
as a product of circles. The homomorphism `Torus.hom : Point → compactIdentityComponent`
is proved to be `ContMDiff` (smooth), establishing the smooth torus inclusion.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule.Torus

noncomputable section

open scoped Manifold Matrix.Norms.L2Operator ContDiff
open TauCeti.DynkinType

attribute [local instance] finrank_real_complex_fact'

/-- Unfold `ModelPi` so that `NormedAddCommGroup` instances are available. -/
noncomputable instance : NormedAddCommGroup
    (ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) :=
  inferInstanceAs (NormedAddCommGroup (Fin 6 → EuclideanSpace ℝ (Fin 1)))

noncomputable instance : NormedSpace ℝ
    (ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) :=
  inferInstanceAs (NormedSpace ℝ (Fin 6 → EuclideanSpace ℝ (Fin 1)))

/-- The torus `Point = Fin 6 → Circle` as a product charted space. -/
noncomputable instance chartedSpacePoint : ChartedSpace
    (ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) Point :=
  piChartedSpace (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)) (fun _ : Fin 6 => Circle)

/-- The power map `z ↦ z ^ n` on `Circle` is `ContMDiff` for any integer `n`. -/
theorem contMDiff_zpow (n : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ n) := by
  rcases em (0 ≤ n) with (hn | hn)
  · lift n to ℕ using hn
    simpa using contMDiff_pow (I := 𝓡 1) (n := ∞) n
  · have hn' : 0 ≤ -n := by linarith
    lift -n to ℕ using hn' with m hm
    have hn_eq : (n : ℤ) = -((m : ℤ)) := by
      linarith
    have h : (fun z : Circle => z ^ n) = (fun z => (z ^ (m : ℤ))⁻¹) := by
      ext z
      rw [hn_eq, zpow_neg]
    rw [h]
    exact (contMDiff_pow (I := 𝓡 1) (n := ∞) m).inv

/-- The projection `Point → Circle` onto the `j`-th factor is `ContMDiff`. -/
theorem contMDiff_proj (j : Fin 6) :
    ContMDiff 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)))
      (𝓡 1) ∞ (fun z : Point => z j) := by
  intro x
  let I := 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)))
  rw [contMDiffAt_iff_source]
  have hI_range : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  rw [hI_range]
  -- Decompose (fun z => z j) ∘ (extChartAt I x).symm
  have h_decomp : (fun (z : Point) => z j) ∘ (extChartAt I x).symm =
      (extChartAt (𝓡 1) (x j)).symm ∘ (fun (θ : ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) => θ j) := by
    funext θ
    dsimp
    -- Goal: ↑(OpenPartialHomeomorph.pi ...).symm (↑I.symm θ) j = ↑(chartAt ... (x j)).symm (θ j)
    -- I is boundaryless, so I.symm is the identity
    have hI_symm : ⇑I.symm = id := by
      have : I.Boundaryless := inferInstance
      ext x; simp [I]
    rw [hI_symm]
    -- Goal: ↑(OpenPartialHomeomorph.pi ...).symm θ j = ↑(chartAt ... (x j)).symm (θ j)
    -- This is true by definition of OpenPartialHomeomorph.pi
    rfl
  rw [h_decomp]
  -- (fun θ => θ j) is ContMDiffAt at (extChartAt I x x)
  have h_proj : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (fun (θ : ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) => θ j)
      (extChartAt I x x) :=
    (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)) (i := j)).contMDiff.contMDiffAt
  -- (extChartAt (𝓡 1) (x j)).symm is ContMDiffAt at (extChartAt (𝓡 1) (x j) (x j))
  have h_symm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡 1) ∞
      (extChartAt (𝓡 1) (x j)).symm (extChartAt (𝓡 1) (x j) (x j)) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓡 1) (n := ∞) (x j)
    have h_range_univ : Set.range (𝓡 1 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) = Set.univ := by
      ext y; simp
    rw [h_range_univ] at h
    exact h.contMDiffAt (by simp)
  -- Match the point: (extChartAt I x x) j = extChartAt (𝓡 1) (x j) (x j)
  have h_point_eq : (extChartAt I x x) j = extChartAt (𝓡 1) (x j) (x j) := by
    simp [I, piChartedSpace_chartAt]
  have h_symm' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡 1) ∞
      (extChartAt (𝓡 1) (x j)).symm ((extChartAt I x x) j) := by
    rw [h_point_eq]
    exact h_symm
  -- Compose
  have h_comp : ContMDiffAt I (𝓡 1) ∞
      ((extChartAt (𝓡 1) (x j)).symm ∘ (fun (θ : ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))) => θ j))
      (extChartAt I x x) :=
    h_symm'.comp (extChartAt I x x) h_proj
  exact h_comp.contMDiffWithinAt

/-- The map `matrix ∘ Torus.hom : Point → Matrix27` is smooth. -/
theorem matrix_hom_contMDiff :
    ContMDiff 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, Matrix27) ∞ (fun z : Point => matrix z) := by
  let I := 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)))
  -- Each component of weights is ContMDiff into Circle
  have h_comp (a : Fin 27) : ContMDiff I (𝓡 1) ∞ (fun z : Point => weights z a) := by
    unfold weights powerMap
    let P : (Point → Circle) → Prop :=
      fun g => ContMDiff I (𝓡 1) ∞ g
    have h_one : P (1 : Point → Circle) := by
      dsimp [P]
      exact contMDiff_const (c := (1 : Circle)) (I := I) (I' := 𝓡 1) (n := ∞)
    have h_mul : ∀ (g1 g2 : Point → Circle), P g1 → P g2 → P (g1 * g2) := by
      intro g1 g2 hg1 hg2
      exact hg1.mul hg2
    have h_factor (j : Fin 6) : P (fun z : Point => z j ^ (e6MinusculeWeight a j)) := by
      dsimp [P]
      exact (contMDiff_zpow (e6MinusculeWeight a j)).comp (contMDiff_proj j)
    have h_base : ∀ j ∈ (Finset.univ : Finset (Fin 6)),
        P (fun z : Point => z j ^ (e6MinusculeWeight a j)) := by
      intro j hj; exact h_factor j
    have h_prod : P (fun z : Point => ∏ j ∈ (Finset.univ : Finset (Fin 6)),
        z j ^ (e6MinusculeWeight a j)) :=
      Finset.prod_induction (s := Finset.univ)
        (f := fun j : Fin 6 => fun z : Point => z j ^ (e6MinusculeWeight a j))
        (p := P) h_mul h_one h_base
    simpa using h_prod
  -- The inclusion Circle → ℂ is ContMDiff
  have h_coe_circle : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun (c : Circle) => (c : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)
  -- Therefore, the map z ↦ (weights z a : ℂ) is ContMDiff
  have h_comp_ℂ (a : Fin 27) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun z : Point => (weights z a : ℂ)) :=
    h_coe_circle.comp (h_comp a)
  -- The map z ↦ (fun a => (weights z a : ℂ)) : Point → Fin 27 → ℂ is ContMDiff
  have h_weights_ℂ : ContMDiff I (𝓘(ℝ, Fin 27 → ℂ)) ∞
      (fun z : Point => fun a : Fin 27 => (weights z a : ℂ)) := by
    rw [contMDiff_pi_space]
    intro a
    simpa using h_comp_ℂ a
  -- The diagonal map (Fin 27 → ℂ) → Matrix27 is ContMDiff (it's continuous and linear)
  have h_diag : ContMDiff 𝓘(ℝ, Fin 27 → ℂ) 𝓘(ℝ, Matrix27) ∞
      (fun d : Fin 27 → ℂ => Matrix.diagonal d) := by
    let f : (Fin 27 → ℂ) →ₗ[ℝ] Matrix27 :=
      { toFun := fun d => Matrix.diagonal d
        map_add' := by
          intro x y
          ext i j
          rw [show (x + y : Fin 27 → ℂ) = (fun i => x i + y i) by rfl]
          rw [(Matrix.diagonal_add x y).symm, Matrix.add_apply]
        map_smul' := by
          intro c x
          ext i j
          -- Goal: diagonal (c • x) i j = ((RingHom.id ℝ) c • diagonal x) i j
          -- Matrix.diagonal_smul c x : diagonal (c • x) = c • diagonal x
          -- And (RingHom.id ℝ) c = c
          simp [RingHom.id_apply] }
    have h_cont : Continuous f := by
      simpa [f] using continuous_id.matrix_diagonal
    let f' : (Fin 27 → ℂ) →L[ℝ] Matrix27 :=
      { f with cont := h_cont }
    exact f'.contMDiff
  -- Compose
  have h_eq : (fun z : Point => matrix z) =
      (fun d : Fin 27 → ℂ => Matrix.diagonal d) ∘
        (fun z : Point => fun a : Fin 27 => (weights z a : ℂ)) := by
    funext z
    simp [matrix, weights, powerMap]
  rw [h_eq]
  exact h_diag.comp h_weights_ℂ

/-- The torus homomorphism `Torus.hom : Point → compactIdentityComponent` is smooth. -/
theorem hom_contMDiff :
    ContMDiff 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, compactMatrixLieAlgebra) ∞ Torus.hom := by
  intro x
  have h := contMDiffAt_of_compactMatrix (I := 𝓘(ℝ, ModelPi (fun _ : Fin 6 => EuclideanSpace ℝ (Fin 1))))
    (f := Torus.hom) (x := x)
    (Torus.hom_continuous.continuousAt)
    (by
      have h_eq : compactMatrix ∘ Torus.hom = (fun z : Point => matrix z) := by
        funext z; simp [Torus.hom_matrix]
      rw [h_eq]
      exact matrix_hom_contMDiff.contMDiffAt (n := ∞) (x := x))
  simpa using h

end

end Math.E6.Minuscule.Torus
