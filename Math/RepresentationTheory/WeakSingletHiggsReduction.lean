import Math.RepresentationTheory.WeakDoubletScalars
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.LinearAlgebra.SelectionCriteria

/-! Downward and upward all-degree reduction for an actual doublet/dual pair
and weak-singlet source. Other group factors remain imposed on the source. -/
namespace Math.WeakSingletHiggsReduction
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct
variable {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
  (a : Representation ℂ G X) (b : Representation ℂ G Doublet)
  (j : WeakDoubletScalars.Group →* G)
  (bweak : ∀ u v, b (j u) v = doublet u v)
  (aweak : ∀ u x, a (j u) x = x)

abbrev Bosons (h d : ℕ) := (b.symmetricPower h).tprod (b.dual.symmetricPower d)
abbrev Coefficients (h d : ℕ) :=
  InvariantCoefficientTransport.Invariants (a.tprod (Bosons b h d))

include bweak in
theorem symmetric_weak (m : ℕ) (u : WeakDoubletScalars.Group) (v : Sym[ℂ]^m Doublet) :
    b.symmetricPower m (j u) v = doublet.symmetricPower m u v := by
  have he : b.symmetricPower m (j u) = doublet.symmetricPower m u := by
    apply SymmetricPower.ext
    intro vv
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod]
    congr 1
    funext i
    exact bweak u (vv i)
  exact DFunLike.congr_fun he v

include bweak in
theorem dual_weak (u : WeakDoubletScalars.Group) (φ : Module.Dual ℂ Doublet) :
    b.dual (j u) φ = doublet.dual u φ := by
  apply LinearMap.ext
  intro v
  change φ (b (j u)⁻¹ v) = φ (doublet u⁻¹ v)
  rw [← map_inv j u,bweak]

include bweak in
theorem dual_symmetric_weak (m : ℕ) (u : WeakDoubletScalars.Group)
    (v : Sym[ℂ]^m (Module.Dual ℂ Doublet)) :
    b.dual.symmetricPower m (j u) v = doublet.dual.symmetricPower m u v := by
  have he : b.dual.symmetricPower m (j u) = doublet.dual.symmetricPower m u := by
    apply SymmetricPower.ext
    intro vv
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod]
    congr 1
    funext i
    exact dual_weak b j bweak u (vv i)
  exact DFunLike.congr_fun he v

include bweak in
theorem bosons_weak (h d : ℕ) (u : WeakDoubletScalars.Group)
    (v : Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d (Module.Dual ℂ Doublet)) :
    Bosons b h d (j u) v =
      ((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)) u v := by
  have he : Bosons b h d (j u) =
      ((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)) u := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change b.symmetricPower h (j u) x ⊗ₜ[ℂ] b.dual.symmetricPower d (j u) y = _
    rw [symmetric_weak b j bweak,dual_symmetric_weak b j bweak]
    rfl
  exact DFunLike.congr_fun he v

include bweak aweak in
def slice (h d : ℕ) (f : Coefficients a b h d) (x : X) : WeakDoubletScalars.Space h d where
  toLinearMap := (TensorProduct.curry f.toLinearMap) x
  isIntertwining' u := by
    apply LinearMap.ext
    intro z
    change f (x ⊗ₜ[ℂ] ((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)) u z) =
      f (x ⊗ₜ[ℂ] z)
    have he := IntertwiningMap.isIntertwining _ _ f (j u) (x ⊗ₜ[ℂ] z)
    change f (a (j u) x ⊗ₜ[ℂ] Bosons b h d (j u) z) = f (x ⊗ₜ[ℂ] z) at he
    rw [aweak,bosons_weak b j bweak] at he
    exact he

include bweak aweak in
theorem unbalanced_zero (h d : ℕ) (hd : h≠d) (f : Coefficients a b h d) : f=0 := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  exact congrArg (fun t : WeakDoubletScalars.Space h d => t z)
    (WeakDoubletScalars.unbalanced_zero h d hd (slice a b j bweak aweak h d f x))

theorem normalized (m : ℕ) : SymmetricDualPairing.coefficient b m (WeakDoubletScalars.probe m) = 1 :=
  WeakDoubletScalars.normalized m

include bweak aweak in
theorem factor (m : ℕ) (f : Coefficients a b m m) (x : X)
    (z : Sym[ℂ]^m Doublet ⊗[ℂ] Sym[ℂ]^m (Module.Dual ℂ Doublet)) :
    f (x ⊗ₜ[ℂ] z) = f (x ⊗ₜ[ℂ] WeakDoubletScalars.probe m) *
      SymmetricDualPairing.coefficient b m z := by
  exact congrArg (fun t : WeakDoubletScalars.Space m m => t z)
    (WeakDoubletScalars.unique m (slice a b j bweak aweak m m f x))

include bweak aweak in
def evaluate (m : ℕ) (f : Coefficients a b m m) :
    InvariantCoefficientTransport.Invariants a where
  toLinearMap := f.toLinearMap.comp
    ((TensorProduct.mk ℂ X (Sym[ℂ]^m Doublet ⊗[ℂ] Sym[ℂ]^m (Module.Dual ℂ Doublet))).flip
      (WeakDoubletScalars.probe m))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change f (a g x ⊗ₜ[ℂ] WeakDoubletScalars.probe m) = f (x ⊗ₜ[ℂ] WeakDoubletScalars.probe m)
    have he := IntertwiningMap.isIntertwining _ _ f g (x ⊗ₜ[ℂ] WeakDoubletScalars.probe m)
    change f (a g x ⊗ₜ[ℂ] Bosons b m m g (WeakDoubletScalars.probe m)) =
      f (x ⊗ₜ[ℂ] WeakDoubletScalars.probe m) at he
    rw [factor a b j bweak aweak] at he
    have hb := IntertwiningMap.isIntertwining _ _ (SymmetricDualPairing.coefficient b m) g
      (WeakDoubletScalars.probe m)
    change SymmetricDualPairing.coefficient b m (Bosons b m m g (WeakDoubletScalars.probe m)) =
      SymmetricDualPairing.coefficient b m (WeakDoubletScalars.probe m) at hb
    rw [normalized b] at hb
    rw [hb,mul_one] at he
    exact he

def assemble (m : ℕ) (f : InvariantCoefficientTransport.Invariants a) : Coefficients a b m m :=
  (Representation.TensorProduct.lid ℂ (trivial ℂ G ℂ)).toIntertwiningMap.comp
    (f.tensor (SymmetricDualPairing.coefficient b m))

theorem assemble_apply (m : ℕ) (f : InvariantCoefficientTransport.Invariants a) (x : X)
    (z : Sym[ℂ]^m Doublet ⊗[ℂ] Sym[ℂ]^m (Module.Dual ℂ Doublet)) :
    assemble a b m f (x ⊗ₜ[ℂ] z) = f x * SymmetricDualPairing.coefficient b m z := rfl

include bweak aweak in
def equiv (m : ℕ) : Coefficients a b m m ≃ₗ[ℂ] InvariantCoefficientTransport.Invariants a where
  toFun := evaluate a b j bweak aweak m
  invFun := assemble a b m
  left_inv f := by
    apply IntertwiningMap.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    exact (factor a b j bweak aweak m f x z).symm
  right_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f x * SymmetricDualPairing.coefficient b m (WeakDoubletScalars.probe m) = f x
    rw [normalized b,mul_one]
  map_add' f g := by ext x; rfl
  map_smul' z f := by ext x; rfl

include bweak aweak in
def zeroDegreeReduction (m : ℕ) : Coefficients a b m m ≃ₗ[ℂ] Coefficients a b 0 0 :=
  (equiv a b j bweak aweak m).trans (equiv a b j bweak aweak 0).symm

include bweak aweak in
theorem allowed_iff (h d : ℕ) : SelectionCriteria.Allowed (Coefficients a b h d) ↔
    h=d ∧ SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants a) := by
  constructor
  · intro hf
    have hd : h=d := by
      by_contra hd
      obtain ⟨f,hn⟩ := hf
      exact hn (unbalanced_zero a b j bweak aweak h d hd f)
    subst d
    exact ⟨rfl,(SelectionCriteria.allowed_equiv (equiv a b j bweak aweak h)).mp hf⟩
  · rintro ⟨rfl,hf⟩
    exact (SelectionCriteria.allowed_equiv (equiv a b j bweak aweak h)).mpr hf

include bweak aweak in
theorem forbidden_iff (h d : ℕ) : SelectionCriteria.Forbidden (Coefficients a b h d) ↔
    h≠d ∨ SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants a) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff a b j bweak aweak,
    not_and_or,SelectionCriteria.forbidden_iff_not_allowed]

include bweak aweak in
theorem all_forbidden_iff : (∀ h d, SelectionCriteria.Forbidden (Coefficients a b h d)) ↔
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants a) := by
  constructor
  · intro hh
    exact ((forbidden_iff a b j bweak aweak 0 0).mp (hh 0 0)).resolve_left (by simp)
  · intro hh h d
    exact (forbidden_iff a b j bweak aweak h d).mpr (Or.inr hh)

include bweak aweak in
theorem all_forbidden_zero_iff : (∀ h d, SelectionCriteria.Forbidden (Coefficients a b h d)) ↔
    SelectionCriteria.Forbidden (Coefficients a b 0 0) :=
  (all_forbidden_iff a b j bweak aweak).trans
    (SelectionCriteria.ofEquiv (equiv a b j bweak aweak 0)).forbidden.symm

end
end Math.WeakSingletHiggsReduction
