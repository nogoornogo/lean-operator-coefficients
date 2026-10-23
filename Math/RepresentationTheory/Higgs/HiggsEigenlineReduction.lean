import Math.RepresentationTheory.Symmetric.SymmetricPowerDescent
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria
import TauCeti.RepresentationTheory.CharacterTwist
import Mathlib.Algebra.Group.Hom.Instances

/-! Arbitrary symmetric degrees for actual one-dimensional scalar carriers.
This is not a weak-doublet decomposition or an SM support classifier. -/
namespace Math.HiggsEigenlineReduction
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct BigOperators

def evaluation (m : ℕ) : Sym[ℂ]^m ℂ →ₗ[ℂ] ℂ :=
  SymmetricPowerDescent.lift m
    ⟨MultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ, by
      intro e v
      exact Equiv.prod_comp e v⟩

@[simp] theorem evaluation_tprod (m : ℕ) (v : Fin m → ℂ) :
    evaluation m (SymmetricPower.tprod ℂ v) = ∏ i, v i :=
  SymmetricPowerDescent.lift_tprod _ _ _

def unitTensor (m : ℕ) : Sym[ℂ]^m ℂ := SymmetricPower.tprod ℂ (fun _ => 1)

@[simp] theorem evaluation_unitTensor (m : ℕ) : evaluation m (unitTensor m) = 1 := by
  simp [unitTensor]

theorem tprod_eq (m : ℕ) (v : Fin m → ℂ) :
    SymmetricPower.tprod ℂ v = (∏ i, v i) • unitTensor m := by
  simpa [unitTensor] using (SymmetricPower.tprod ℂ).map_smul_univ v (fun _ => (1 : ℂ))

theorem reconstruct (m : ℕ) (v : Sym[ℂ]^m ℂ) :
    evaluation m v • unitTensor m = v := by
  have he : (LinearMap.id : Sym[ℂ]^m ℂ →ₗ[ℂ] Sym[ℂ]^m ℂ) =
      (evaluation m).smulRight (unitTensor m) := by
    apply SymmetricPower.ext
    intro w
    exact (tprod_eq m w).trans (by simp)
  exact (DFunLike.congr_fun he v).symm

def lineEquiv (m : ℕ) : Sym[ℂ]^m ℂ ≃ₗ[ℂ] ℂ where
  toLinearMap := evaluation m
  invFun z := z • unitTensor m
  left_inv := reconstruct m
  right_inv z := by simp

variable {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
  (χ : G →* ℂˣ) (a : Representation ℂ G X)

def powerEquiv (m : ℕ) :
    Representation.Equiv ((ofLinearCharacter χ).symmetricPower m)
      (ofLinearCharacter (χ^m)) :=
  Representation.Equiv.mk (lineEquiv m) (by
    intro g
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) ℂ)
    rintro _ ⟨v,rfl⟩
    simp [lineEquiv,
      ofLinearCharacter_apply, Finset.prod_mul_distrib])

/-- The split symmetric powers retain Higgs and dual-Higgs degrees separately. -/
abbrev Bosons (h d : ℕ) :=
  ((ofLinearCharacter χ).symmetricPower h).tprod
    ((ofLinearCharacter χ⁻¹).symmetricPower d)

abbrev Coefficients (h d : ℕ) :=
  InvariantCoefficientTransport.Invariants (a.tprod (Bosons χ h d))

def pairEquiv (h d : ℕ) : Representation.Equiv (Bosons χ h d)
    (ofLinearCharacter (χ^h * χ⁻¹^d)) :=
  Representation.Equiv.mk
    ((TensorProduct.congr (lineEquiv h) (lineEquiv d)).trans (TensorProduct.lid ℂ ℂ)) (by
      intro g
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      have hu := IntertwiningMap.isIntertwining _ _ (powerEquiv χ h).toIntertwiningMap g u
      have hv := IntertwiningMap.isIntertwining _ _ (powerEquiv χ⁻¹ d).toIntertwiningMap g v
      change evaluation h (((ofLinearCharacter χ).symmetricPower h) g u) *
        evaluation d (((ofLinearCharacter χ⁻¹).symmetricPower d) g v) = _
      change evaluation h (((ofLinearCharacter χ).symmetricPower h) g u) =
        ((χ g : ℂ)^h) * evaluation h u at hu
      change evaluation d (((ofLinearCharacter χ⁻¹).symmetricPower d) g v) =
        (((χ⁻¹) g : ℂ)^d) * evaluation d v at hv
      rw [hu,hv]
      change _ = ((χ g : ℂ)^h * (((χ⁻¹) g : ℂ)^d)) * (evaluation h u * evaluation d v)
      ring)

def sourceEquiv (h d : ℕ) : Representation.Equiv (a.tprod (Bosons χ h d))
    (charTwist (χ^h * χ⁻¹^d) a) :=
  (Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl ℂ X) (pairEquiv χ h d).toLinearEquiv) (by
      intro g
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro v
      have he := IntertwiningMap.isIntertwining _ _ (pairEquiv χ h d).toIntertwiningMap g v
      change a g x ⊗ₜ[ℂ] (pairEquiv χ h d) ((Bosons χ h d) g v) =
        a g x ⊗ₜ[ℂ] (ofLinearCharacter (χ^h * χ⁻¹^d)) g ((pairEquiv χ h d) v)
      exact congrArg (fun w => a g x ⊗ₜ[ℂ] w) he)).trans
      (tprodOfLinearCharacterEquivCharTwist (χ^h * χ⁻¹^d) a)

/-- Both inverse identities come from actual carrier equivalences. -/
def coefficientEquiv (h d : ℕ) : Coefficients χ a h d ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants (charTwist (χ^h * χ⁻¹^d) a) :=
  InvariantCoefficientTransport.alongEquiv (sourceEquiv χ a h d)

theorem sourceEquiv_unit (h d : ℕ) (x : X) :
    sourceEquiv χ a h d (x ⊗ₜ[ℂ] (unitTensor h ⊗ₜ[ℂ] unitTensor d)) = x := by
  change (evaluation h (unitTensor h) * evaluation d (unitTensor d)) • x = x
  simp

/-- Downward transport is evaluation on the two canonical unit tensors. -/
theorem coefficientEquiv_apply (h d : ℕ) (f : Coefficients χ a h d) (x : X) :
    coefficientEquiv χ a h d f x =
      f (x ⊗ₜ[ℂ] (unitTensor h ⊗ₜ[ℂ] unitTensor d)) := by
  change f ((sourceEquiv χ a h d).symm x) = _
  have he := congrArg (sourceEquiv χ a h d).symm (sourceEquiv_unit χ a h d x)
  exact congrArg f (he.symm.trans
    ((sourceEquiv χ a h d).toLinearEquiv.symm_apply_apply _))

def reduction (h d h' d' : ℕ) (he : χ^h * χ⁻¹^d = χ^h' * χ⁻¹^d') :
    Coefficients χ a h d ≃ₗ[ℂ] Coefficients χ a h' d' :=
  (coefficientEquiv χ a h d).trans (by
    rw [he]
    exact (coefficientEquiv χ a h' d').symm)

theorem cancel_character (h d r : ℕ) :
    χ^(h+r) * χ⁻¹^(d+r) = χ^h * χ⁻¹^d := by
  rw [_root_.pow_add χ h r, _root_.pow_add χ⁻¹ d r]
  rw [mul_mul_mul_comm (χ^h) (χ^r) (χ⁻¹^d) (χ⁻¹^r), _root_.inv_pow χ r]
  rw [mul_inv_cancel, mul_one]

/-- No seed premise is required to remove arbitrarily many neutral pairs. -/
def cancelPairs (h d r : ℕ) :
    Coefficients χ a (h+r) (d+r) ≃ₗ[ℂ] Coefficients χ a h d :=
  reduction χ a _ _ _ _ (cancel_character χ h d r)

/-- Remove all common insertions; no finite-order character is needed. -/
def primitiveReduction (h d : ℕ) :
    Coefficients χ a h d ≃ₗ[ℂ] Coefficients χ a (h-min h d) (d-min h d) := by
  have eh : h-min h d+min h d=h := Nat.sub_add_cancel (Nat.min_le_left h d)
  have ed : d-min h d+min h d=d := Nat.sub_add_cancel (Nat.min_le_right h d)
  exact reduction χ a h d (h-min h d) (d-min h d)
    ((congrArg₂ (fun u v : ℕ => χ^u * χ⁻¹^v) eh ed).symm.trans
      (cancel_character χ (h-min h d) (d-min h d) (min h d)))

theorem primitive_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (Coefficients χ a h d) ↔
      SelectionCriteria.Allowed (Coefficients χ a (h-min h d) (d-min h d)) :=
  SelectionCriteria.allowed_equiv (primitiveReduction χ a h d)

theorem primitive_forbidden_iff (h d : ℕ) :
    SelectionCriteria.Forbidden (Coefficients χ a h d) ↔
      SelectionCriteria.Forbidden (Coefficients χ a (h-min h d) (d-min h d)) :=
  (SelectionCriteria.ofEquiv (primitiveReduction χ a h d)).forbidden

theorem balanced_allowed_iff (r : ℕ) :
    SelectionCriteria.Allowed (Coefficients χ a r r) ↔
      SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants a) := by
  have he := SelectionCriteria.allowed_equiv (coefficientEquiv χ a r r)
  have hc : χ^r * χ⁻¹^r = 1 := by
    rw [_root_.inv_pow χ r,mul_inv_cancel]
  have ht : charTwist (χ^r * χ⁻¹^r) a = a :=
    (congrArg (fun ψ : G →* ℂˣ => charTwist ψ a) hc).trans (charTwist_one a)
  rw [ht] at he
  exact he

theorem character_mod (k m : ℕ) (period : χ^k=1) : χ^m = χ^(m%k) := by
  apply MonoidHom.ext
  intro g
  have hp : χ g ^ k = 1 := congrArg (fun ψ : G →* ℂˣ => ψ g) period
  change χ g ^ m = χ g ^ (m%k)
  conv_lhs => rw [← Nat.mod_add_div m k]
  rw [pow_add,pow_mul,hp,one_pow,mul_one]

/-- A positive period gives a finite square of tests, independent of source dimension. -/
def finiteReduction (k : ℕ) (period : χ^k=1) (h d : ℕ) :
    Coefficients χ a h d ≃ₗ[ℂ] Coefficients χ a (h%k) (d%k) :=
  reduction χ a _ _ _ _ (by
    rw [character_mod χ k h period, character_mod χ⁻¹ k d
      (by
        apply MonoidHom.ext
        intro g
        have hp : χ g ^ k = 1 := congrArg (fun ψ : G →* ℂˣ => ψ g) period
        change (χ g)⁻¹ ^ k = (1 : ℂˣ)
        rw [inv_pow,hp,inv_one])])

theorem allowed_mod (k : ℕ) (period : χ^k=1) (h d : ℕ) :
    SelectionCriteria.Allowed (Coefficients χ a h d) ↔
      SelectionCriteria.Allowed (Coefficients χ a (h%k) (d%k)) :=
  SelectionCriteria.allowed_equiv (finiteReduction χ a k period h d)

theorem forbidden_mod (k : ℕ) (period : χ^k=1) (h d : ℕ) :
    SelectionCriteria.Forbidden (Coefficients χ a h d) ↔
      SelectionCriteria.Forbidden (Coefficients χ a (h%k) (d%k)) :=
  (SelectionCriteria.ofEquiv (finiteReduction χ a k period h d)).forbidden

theorem all_forbidden_iff (k : ℕ) (hk : 0<k) (period : χ^k=1) :
    (∀ h d, SelectionCriteria.Forbidden (Coefficients χ a h d)) ↔
      ∀ h d : Fin k, SelectionCriteria.Forbidden (Coefficients χ a h.val d.val) := by
  constructor
  · intro hh h d; exact hh h.val d.val
  · intro hh h d
    exact (forbidden_mod χ a k period h d).mpr
      (hh ⟨h%k,Nat.mod_lt h hk⟩ ⟨d%k,Nat.mod_lt d hk⟩)

theorem complement_character (k : ℕ) (hk : 0<k) (period : χ^k=1) (d : ℕ) :
    χ⁻¹^d = χ^(k-d%k) := by
  apply MonoidHom.ext
  intro g
  have hp : χ g ^ k = 1 := congrArg (fun ψ : G →* ℂˣ => ψ g) period
  have hm : χ g ^ d = χ g ^ (d%k) :=
    congrArg (fun ψ : G →* ℂˣ => ψ g) (character_mod χ k d period)
  change (χ g)⁻¹^d = χ g ^ (k-d%k)
  rw [inv_pow,hm,pow_sub _ (Nat.le_of_lt (Nat.mod_lt d hk)),hp,one_mul]

/-- Remove redundancy in the square: k one-axis spaces suffice. -/
def singleAxisReduction (k : ℕ) (hk : 0<k) (period : χ^k=1) (h d : ℕ) :
    Coefficients χ a h d ≃ₗ[ℂ] Coefficients χ a ((h+(k-d%k))%k) 0 :=
  reduction χ a _ _ _ _ (by
    rw [complement_character χ k hk period d, ← _root_.pow_add χ h (k-d%k),
      character_mod χ k (h+(k-d%k)) period]
    apply MonoidHom.ext
    intro g
    change χ g ^ ((h+(k-d%k))%k) = χ g ^ ((h+(k-d%k))%k) * (χ g)⁻¹^0
    rw [pow_zero,mul_one])

theorem all_forbidden_single_iff (k : ℕ) (hk : 0<k) (period : χ^k=1) :
    (∀ h d, SelectionCriteria.Forbidden (Coefficients χ a h d)) ↔
      ∀ j : Fin k, SelectionCriteria.Forbidden (Coefficients χ a j.val 0) := by
  constructor
  · intro hh j; exact hh j.val 0
  · intro hh h d
    exact (SelectionCriteria.ofEquiv (singleAxisReduction χ a k hk period h d)).forbidden.mpr
      (hh ⟨(h+(k-d%k))%k,Nat.mod_lt _ hk⟩)

theorem exists_allowed_single_iff (k : ℕ) (hk : 0<k) (period : χ^k=1) :
    (∃ h d, SelectionCriteria.Allowed (Coefficients χ a h d)) ↔
      ∃ j : Fin k, SelectionCriteria.Allowed (Coefficients χ a j.val 0) := by
  constructor
  · rintro ⟨h,d,ha⟩
    exact ⟨⟨(h+(k-d%k))%k,Nat.mod_lt _ hk⟩,
      (SelectionCriteria.allowed_equiv (singleAxisReduction χ a k hk period h d)).mp ha⟩
  · rintro ⟨j,hj⟩; exact ⟨j.val,0,hj⟩

section SuppliedEigenlines
variable {B D : Type*} [AddCommGroup B] [Module ℂ B] [AddCommGroup D] [Module ℂ D]
  {b : Representation ℂ G B} {d : Representation ℂ G D}

/-- Transport a certified eigenline input; an embedding into a larger Higgs
space does not suffice to apply this equivalence to that larger space. -/
def alongLines (e : Representation.Equiv b (ofLinearCharacter χ))
    (f : Representation.Equiv d (ofLinearCharacter χ⁻¹)) (h j : ℕ) :
    InvariantCoefficientTransport.Invariants
      (a.tprod ((b.symmetricPower h).tprod (d.symmetricPower j))) ≃ₗ[ℂ]
        Coefficients χ a h j :=
  InvariantCoefficientTransport.alongEquiv
    (ExternalInvariantTensor.tensorEquiv (Representation.Equiv.refl a)
      (ExternalInvariantTensor.tensorEquiv (e.symmetricPower h) (f.symmetricPower j)))

end SuppliedEigenlines

theorem line_allowed_iff (ψ : G →* ℂˣ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (ofLinearCharacter ψ)) ↔
      ψ=1 := by
  constructor
  · rintro ⟨f,hf⟩
    have hn : f (1 : ℂ) ≠ 0 := by
      intro hz
      apply hf
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      have he := f.toLinearMap.map_smul z (1 : ℂ)
      simp only [smul_eq_mul,mul_one] at he
      change f z = z * f 1 at he
      change f z = 0
      rw [he,hz,mul_zero]
    apply MonoidHom.ext
    intro g
    apply Units.ext
    have he := IntertwiningMap.isIntertwining _ _ f g (1 : ℂ)
    have hh : (ψ g : ℂ) * f 1 = f 1 := by
      change f ((ψ g : ℂ) • (1 : ℂ)) = f 1 at he
      exact (f.toLinearMap.map_smul (ψ g : ℂ) (1 : ℂ)).symm.trans he
    exact mul_right_cancel₀ hn (hh.trans (one_mul (f 1)).symm)
  · intro hp
    subst ψ
    let f : InvariantCoefficientTransport.Invariants
        (ofLinearCharacter (1 : G →* ℂˣ)) :=
      { toLinearMap := LinearMap.id
        isIntertwining' g := by simp }
    refine ⟨f,?_⟩
    intro hz
    have he := congrArg (fun t : InvariantCoefficientTransport.Invariants
      (ofLinearCharacter (1 : G →* ℂˣ)) => t (1 : ℂ)) hz
    change (1 : ℂ) = 0 at he
    exact one_ne_zero he

/-- A concrete source-character control: the complete support condition is
neutrality of the total character, not a supplied seed. -/
theorem scalar_source_allowed_iff (ψ : G →* ℂˣ) (h d : ℕ) :
    SelectionCriteria.Allowed (Coefficients χ (ofLinearCharacter ψ) h d) ↔
      (χ^h * χ⁻¹^d) * ψ = 1 := by
  have ht : charTwist (χ^h * χ⁻¹^d) (ofLinearCharacter ψ) =
      ofLinearCharacter ((χ^h * χ⁻¹^d) * ψ) := by
    rw [← charTwist_trivial ψ,charTwist_charTwist,charTwist_trivial]
  have he := SelectionCriteria.allowed_equiv
    (coefficientEquiv χ (ofLinearCharacter ψ) h d)
  rw [ht] at he
  exact he.trans (line_allowed_iff _)

end
end Math.HiggsEigenlineReduction
