import Math.LinearAlgebra.BinaryExteriorProduct
import Math.RepresentationTheory.PatternExteriorSource
import Math.RepresentationTheory.ExteriorCharacterPolynomial

/-! Actual statistical sources with two distinct species blocks. -/
namespace Math.BinaryPatternExterior
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {S G : Type*} [Fintype S] [DecidableEq S] [Group G]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s)) (s t : S) (n m : ℕ)

def pattern : Fin (n+m) → S := Fin.append (fun _ => s) (fun _ => t)

def inclusion : V s × V t →ₗ[ℂ] (∀ a, V a) :=
  (LinearMap.single ℂ V s).comp (LinearMap.fst ℂ (V s) (V t)) +
    (LinearMap.single ℂ V t).comp (LinearMap.snd ℂ (V s) (V t))

def raw : (⋀[ℂ]^n (V s)) ⊗[ℂ] (⋀[ℂ]^m (V t)) →ₗ[ℂ]
    ⋀[ℂ]^(n+m) (∀ a, V a) :=
  (exteriorPower.map (n+m) (inclusion (V := V) s t)).comp (BinaryExteriorProduct.map n m)

def values (v : Fin n → V s) (w : Fin m → V t) : ∀ i, V (pattern s t n m i) :=
  fun i => (Fin.append (fun j => Pi.single s (v j)) (fun j => Pi.single t (w j)) i)
    (pattern s t n m i)

omit [Fintype S] [∀ s, Module ℂ (V s)] in
private theorem single_project {a b : S} (h : a = b) (x : V b) :
    Pi.single a (Pi.single b x a) = Pi.single b x := by
  subst a
  simp

omit [Fintype S] [∀ s, Module ℂ (V s)] in
private theorem single_cast {a b : S} (h : a = b) (x : V a) :
    Pi.single b (cast (congrArg V h) x) a = x := by
  subst b
  simp

theorem raw_pure (v : Fin n → V s) (w : Fin m → V t) :
    raw (V := V) s t n m ((exteriorPower.ιMulti ℂ n v) ⊗ₜ[ℂ] (exteriorPower.ιMulti ℂ m w)) =
      (PatternExteriorSource.pure r (pattern s t n m) (values s t n m v w)).val := by
  rw [raw, LinearMap.comp_apply, BinaryExteriorProduct.map_pure,
    exteriorPower.map_apply_ιMulti, PatternExteriorSource.pure_val]
  apply congrArg (exteriorPower.ιMulti ℂ (n+m))
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [values, Function.comp_apply, Fin.append_left]
    simp only [inclusion, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.inl_apply, map_zero, add_zero,
      LinearMap.single_apply]
    exact (single_project (Fin.append_left (fun _ : Fin n => s) (fun _ : Fin m => t) j) (v j)).symm
  · intro j
    simp only [values, Function.comp_apply, Fin.append_right]
    simp only [inclusion, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.inr_apply, map_zero, zero_add,
      LinearMap.single_apply]
    exact (single_project (Fin.append_right (fun _ : Fin n => s) (fun _ : Fin m => t) j) (w j)).symm

def forward : (⋀[ℂ]^n (V s)) ⊗[ℂ] (⋀[ℂ]^m (V t)) →ₗ[ℂ]
    PatternExteriorSource.Source r (pattern s t n m) :=
  (PatternExteriorSource.projectionLinear r (pattern s t n m)).comp (raw s t n m)

theorem forward_pure (v : Fin n → V s) (w : Fin m → V t) :
    forward r s t n m ((exteriorPower.ιMulti ℂ n v) ⊗ₜ[ℂ] (exteriorPower.ιMulti ℂ m w)) =
      PatternExteriorSource.pure r (pattern s t n m) (values s t n m v w) := by
  rw [forward, LinearMap.comp_apply, raw_pure r]
  exact PatternExteriorSource.projection_inclusion r _ _

theorem inclusion_forward :
    (PatternExteriorSource.Source r (pattern s t n m)).subtype.comp (forward r s t n m) =
      raw s t n m := by
  apply BinaryExteriorProduct.ext
  intro v w
  change (forward r s t n m ((exteriorPower.ιMulti ℂ n v) ⊗ₜ[ℂ]
    (exteriorPower.ιMulti ℂ m w))).val = _
  rw [forward_pure, raw_pure r]

omit [Fintype S] in
theorem inclusion_injective (hst : s ≠ t) : Function.Injective (inclusion (V := V) s t) := by
  intro x y h
  apply Prod.ext
  · have hs := congrFun h s
    simpa [inclusion, hst, hst.symm] using hs
  · have ht := congrFun h t
    simpa [inclusion, hst, hst.symm] using ht

theorem forward_injective (hst : s ≠ t) : Function.Injective (forward r s t n m) := by
  have hi := (exteriorPower.map_injective_field (n := n+m) (inclusion_injective s t hst)).comp
    (BinaryExteriorProduct.injective (K := ℂ) (M := V s) (N := V t) n m)
  intro x y h
  apply hi
  exact (LinearMap.congr_fun (inclusion_forward r s t n m) x).symm.trans
    ((congrArg Subtype.val h).trans (LinearMap.congr_fun (inclusion_forward r s t n m) y))

def leftValues (v : ∀ i, V (pattern s t n m i)) : Fin n → V s := fun j =>
  cast (congrArg V (Fin.append_left (fun _ : Fin n => s) (fun _ : Fin m => t) j))
    (v (Fin.castAdd m j))

def rightValues (v : ∀ i, V (pattern s t n m i)) : Fin m → V t := fun j =>
  cast (congrArg V (Fin.append_right (fun _ : Fin n => s) (fun _ : Fin m => t) j))
    (v (Fin.natAdd n j))

omit [Fintype S] [∀ s, Module ℂ (V s)] in
theorem values_reconstruct (v : ∀ i, V (pattern s t n m i)) :
    values s t n m (leftValues s t n m v) (rightValues s t n m v) = v := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [values, leftValues, Fin.append_left]
    exact single_cast (Fin.append_left _ _ j) (v (Fin.castAdd m j))
  · intro j
    simp only [values, rightValues, Fin.append_right]
    exact single_cast (Fin.append_right _ _ j) (v (Fin.natAdd n j))

theorem forward_surjective : Function.Surjective (forward r s t n m) := by
  have h : LinearMap.range (PatternExteriorSource.onto r (pattern s t n m)).toLinearMap ≤
      LinearMap.range (forward r s t n m) := by
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨(exteriorPower.ιMulti ℂ n (leftValues s t n m v)) ⊗ₜ[ℂ]
      (exteriorPower.ιMulti ℂ m (rightValues s t n m v)), ?_⟩
    rw [forward_pure, values_reconstruct]
    rfl
  have ht := LinearMap.range_eq_top.mpr (PatternExteriorSource.onto_surjective r (pattern s t n m))
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (ht ▸ h))

def linearEquiv (hst : s ≠ t) : (⋀[ℂ]^n (V s)) ⊗[ℂ] (⋀[ℂ]^m (V t)) ≃ₗ[ℂ]
    PatternExteriorSource.Source r (pattern s t n m) :=
  LinearEquiv.ofBijective (forward r s t n m)
    ⟨forward_injective r s t n m hst, forward_surjective r s t n m⟩

theorem raw_action (g : G) :
    (raw (V := V) s t n m).comp (((r s).exteriorPower n).tprod ((r t).exteriorPower m) g) =
      ((FiniteSpeciesExterior.representation r).exteriorPower (n+m) g).comp (raw s t n m) := by
  apply BinaryExteriorProduct.ext
  intro v w
  simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    Representation.exteriorPower_apply_ιMulti, raw, BinaryExteriorProduct.map_pure,
    exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti ℂ (n+m))
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply, Fin.append_left]
    simp only [inclusion, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.inl_apply, map_zero, add_zero, LinearMap.single_apply]
    exact (FiniteSpeciesExterior.action_single r g s (v j)).symm
  · intro j
    simp only [Function.comp_apply, Fin.append_right]
    simp only [inclusion, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.inr_apply, map_zero, zero_add, LinearMap.single_apply]
    exact (FiniteSpeciesExterior.action_single r g t (w j)).symm

def equiv (hst : s ≠ t) :
    Representation.Equiv (((r s).exteriorPower n).tprod ((r t).exteriorPower m))
      (PatternExteriorSource.representation r (pattern s t n m)) where
  toLinearEquiv := linearEquiv r s t n m hst
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (forward r s t n m
      ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)) g x)).val =
      ((FiniteSpeciesExterior.representation r).exteriorPower (n+m)) g
        (forward r s t n m x).val
    have h₁ := LinearMap.congr_fun (inclusion_forward r s t n m)
      ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)) g x)
    have h₂ := LinearMap.congr_fun (inclusion_forward r s t n m) x
    change (forward r s t n m _).val = raw s t n m _ at h₁
    change (forward r s t n m x).val = raw s t n m x at h₂
    exact h₁.trans ((LinearMap.congr_fun (raw_action r s t n m g) x).trans
      (congrArg (((FiniteSpeciesExterior.representation r).exteriorPower (n+m)) g) h₂.symm))

theorem dimension [FiniteDimensional ℂ (V s)] [FiniteDimensional ℂ (V t)] (hst : s ≠ t) :
    Module.finrank ℂ (PatternExteriorSource.Source r (pattern s t n m)) =
      (Module.finrank ℂ (V s)).choose n * (Module.finrank ℂ (V t)).choose m := by
  rw [← (linearEquiv r s t n m hst).finrank_eq, Module.finrank_tensorProduct,
    exteriorPower.finrank_eq, exteriorPower.finrank_eq]

theorem character [FiniteDimensional ℂ (V s)] [FiniteDimensional ℂ (V t)] (hst : s ≠ t) (g : G) :
    (PatternExteriorSource.representation r (pattern s t n m)).character g =
      ((r s).exteriorPower n).character g * ((r t).exteriorPower m).character g := by
  let : AddCommGroup ((⋀[ℂ]^n (V s)) ⊗[ℂ] (⋀[ℂ]^m (V t))) :=
    Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (PatternExteriorSource.Source r (pattern s t n m)) :=
    Module.addCommMonoidToAddCommGroup ℂ
  let e := equiv r s t n m hst
  change LinearMap.trace ℂ _ ((PatternExteriorSource.representation r (pattern s t n m)) g) = _
  rw [← e.conj_apply_self]
  calc
    _ = LinearMap.trace ℂ _ ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)) g) := by
      convert! LinearMap.trace_conj'
        ((((r s).exteriorPower n).tprod ((r t).exteriorPower m)) g) e.toLinearEquiv
    _ = _ := by
      convert! LinearMap.trace_tensorProduct' (((r s).exteriorPower n) g) (((r t).exteriorPower m) g)

theorem character_diagonal {I J : Type*} [Fintype I] [Fintype J]
    (b : Module.Basis I ℂ (V s)) (c : Module.Basis J ℂ (V t))
    (hst : s ≠ t) (g : G) (a : I → ℂ) (d : J → ℂ)
    (ha : ∀ i, r s g (b i) = a i • b i) (hd : ∀ j, r t g (c j) = d j • c j) :
    (PatternExteriorSource.representation r (pattern s t n m)).character g =
      (ExteriorCharacterPolynomial.generating a).coeff n *
        (ExteriorCharacterPolynomial.generating d).coeff m := by
  have : FiniteDimensional ℂ (V s) := Module.Finite.of_basis b
  have : FiniteDimensional ℂ (V t) := Module.Finite.of_basis c
  rw [character r s t n m hst g,
    ExteriorCharacterPolynomial.exterior_character (r s) b g a ha n,
    ExteriorCharacterPolynomial.exterior_character (r t) c g d hd m]

end
end Math.BinaryPatternExterior
