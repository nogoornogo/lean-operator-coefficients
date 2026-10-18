import Physics.FieldTheory.Yukawa.ProjectedYukawa

/-! Evaluation interfaces avoiding expansion of concrete representation carriers. -/
set_option autoImplicit false
namespace GUT.ProjectedYukawa
noncomputable section
open Representation WeylYukawaMass
variable {G S V : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup V] [Module ℂ V]
  {s : Representation ℂ G S} {r : Representation ℂ G V}

theorem diagonal_apply (Y : EquivariantYukawa s r) (p : IntertwiningMap r r)
    (v : S) (x y : V) :
    (diagonal Y p).toLinearMap v x y = Y.toLinearMap v (p x) (p y) := rfl

theorem mixed_apply (Y : EquivariantYukawa s r) (p q : IntertwiningMap r r)
    (v : S) (x y : V) : (mixed Y p q).toLinearMap v x y =
      Y.toLinearMap v (p x) (q y) + Y.toLinearMap v (q x) (p y) := rfl

theorem combine_apply (Y Z : EquivariantYukawa s r) (a b : ℂ)
    (v : S) (x y : V) : (combine Y Z a b).toLinearMap v x y =
      a * Y.toLinearMap v x y + b * Z.toLinearMap v x y := rfl

theorem zeroBare_form {K : Type*} [Group K] (Y : EquivariantYukawa s r)
    (f : K →* G) (v : S) (hv : ∀ k, s (f k) v = v) :
    (atVacuumOn (InvariantWeylMass.SymmetricMass.zero r) Y f v hv).form =
      Y.toLinearMap v := zero_add _

def fiveFamily (Y : EquivariantYukawa s r)
    (p r0 r1 s0 t0 s1 : IntertwiningMap r r) (a b u v w : ℂ) :=
  combine (combine (mixed Y p r0) (mixed Y p r1) a b)
    (combine (combine (diagonal Y s0) (mixed Y t0 r1) (u / 2) v)
      (diagonal Y s1) 1 (w / 2)) 1 1

def fiveForm (B : LinearMap.BilinForm ℂ V) (p r0 r1 s0 t0 s1 : V →ₗ[ℂ] V)
    (a b u v w : ℂ) : LinearMap.BilinForm ℂ V :=
  a • (B.compl₁₂ p r0 + B.compl₁₂ r0 p) +
  b • (B.compl₁₂ p r1 + B.compl₁₂ r1 p) +
  (u / 2) • B.compl₁₂ s0 s0 +
  v • (B.compl₁₂ t0 r1 + B.compl₁₂ r1 t0) +
  (w / 2) • B.compl₁₂ s1 s1

theorem fiveFamily_form {K : Type*} [Group K] (Y : EquivariantYukawa s r)
    (p r0 r1 s0 t0 s1 : IntertwiningMap r r) (a b u v w : ℂ)
    (f : K →* G) (vac : S) (hv : ∀ k, s (f k) vac = vac)
    (B : LinearMap.BilinForm ℂ V) (hB : Y.toLinearMap vac = B) :
    (atVacuumOn (InvariantWeylMass.SymmetricMass.zero r)
      (fiveFamily Y p r0 r1 s0 t0 s1 a b u v w) f vac hv).form =
      fiveForm B p.toLinearMap r0.toLinearMap r1.toLinearMap s0.toLinearMap
        t0.toLinearMap s1.toLinearMap a b u v w := by
  rw [zeroBare_form]
  ext x y
  simp only [fiveFamily, combine_apply, mixed_apply, diagonal_apply, hB,
    fiveForm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    smul_eq_mul, one_mul, IntertwiningMap.coe_toLinearMap]
  ring

theorem fiveForm_coordinates {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (F : LinearMap.BilinForm ℂ ((A × B) × B))
    (K : A → B → ℂ) (t : B → ℂ)
    (hK0 : ∀ z, K 0 z = 0) (ht : t 0 = 0)
    (p r0 r1 s0 t0 s1 : ((A × B) × B) →ₗ[ℂ] ((A × B) × B))
    (hF : ∀ x y, F x y = K x.1.1 y.2 + t x.1.2 * t y.2 +
      K y.1.1 x.2 + t y.1.2 * t x.2)
    (hp : ∀ x, p x = ((x.1.1, 0), 0))
    (hr0 : ∀ x, r0 x = ((0, 0), x.1.2))
    (hr1 : ∀ x, r1 x = ((0, 0), x.2))
    (hs0 : ∀ x, s0 x = ((0, x.1.2), x.1.2))
    (ht0 : ∀ x, t0 x = ((0, x.1.2), 0))
    (hs1 : ∀ x, s1 x = ((0, x.2), x.2))
    (a b u v w : ℂ) (x y : (A × B) × B) :
    fiveForm F p r0 r1 s0 t0 s1 a b u v w x y =
      a * (K x.1.1 y.1.2 + K y.1.1 x.1.2) +
      b * (K x.1.1 y.2 + K y.1.1 x.2) +
      u * (t x.1.2 * t y.1.2) +
      v * (t x.1.2 * t y.2 + t x.2 * t y.1.2) + w * (t x.2 * t y.2) := by
  simp only [fiveForm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    hF, hp, hr0, hr1, hs0, ht0, hs1, hK0, ht, smul_eq_mul]
  ring

def flavorLinear {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (a b c d : ℂ) :
    ((A × B) × B) →ₗ[ℂ] ((A × B) × B) where
  toFun x := ((0, a • x.1.2 + b • x.2), c • x.1.2 + d • x.2)
  map_add' := by intros; simp [smul_add, add_add_add_comm]
  map_smul' := by intros; simp [smul_add, smul_smul, mul_comm]

theorem fiveForm_flavor_coordinates {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (F : LinearMap.BilinForm ℂ ((A × B) × B))
    (K : A → B → ℂ) (t : B → ℂ)
    (hK0 : ∀ z, K 0 z = 0) (ht : t 0 = 0)
    (p : ((A × B) × B) →ₗ[ℂ] ((A × B) × B))
    (hF : ∀ x y, F x y = K x.1.1 y.2 + t x.1.2 * t y.2 +
      K y.1.1 x.2 + t y.1.2 * t x.2)
    (hp : ∀ x, p x = ((x.1.1, 0), 0))
    (a b u v w : ℂ) (x y : (A × B) × B) :
    fiveForm F p (flavorLinear 0 0 1 0) (flavorLinear 0 0 0 1)
      (flavorLinear 1 0 1 0) (flavorLinear 1 0 0 0) (flavorLinear 0 1 0 1)
      a b u v w x y =
      a * (K x.1.1 y.1.2 + K y.1.1 x.1.2) +
      b * (K x.1.1 y.2 + K y.1.1 x.2) +
      u * (t x.1.2 * t y.1.2) +
      v * (t x.1.2 * t y.2 + t x.2 * t y.1.2) + w * (t x.2 * t y.2) := by
  exact fiveForm_coordinates F K t hK0 ht p
    (flavorLinear 0 0 1 0) (flavorLinear 0 0 0 1) (flavorLinear 1 0 1 0)
    (flavorLinear 1 0 0 0) (flavorLinear 0 1 0 1)
    hF hp (by intro z; simp [flavorLinear]) (by intro z; simp [flavorLinear])
    (by intro z; simp [flavorLinear]) (by intro z; simp [flavorLinear])
    (by intro z; simp [flavorLinear]) a b u v w x y

end
end GUT.ProjectedYukawa
