import GUT.PatiSalam.Embeddings.ComponentRepresentations

/-! The bidoublet as Hom(right,left): its columns have 6Y=-3,+3.
This dual-index convention is explicit; no EW vacuum-selection theorem. -/
namespace GUT.PatiSalam.PhiRepresentation
set_option autoImplicit false
noncomputable section
open StandardSMGaugeTensor StandardModelEmbedding ComponentRepresentations
abbrev Phi := Two →ₗ[ℂ] Two

def representation : Representation ℂ PSGroup Phi := Representation.linHom right left

def join (x : Two × Two) : Phi :=
  (LinearMap.proj 0).smulRight x.1 + (LinearMap.proj 1).smulRight x.2

def split (f : Phi) : Two × Two := (f (Pi.single 0 1), f (Pi.single 1 1))

@[simp] theorem split_join (x : Two × Two) : split (join x) = x := by
  simp [split,join]

theorem join_split (f : Phi) : join (split f) = f := by
  apply LinearMap.ext
  intro w
  funext i
  have hw : w = w 0 • (Pi.single 0 1 : Two) + w 1 • (Pi.single 1 1 : Two) := by
    ext j
    fin_cases j <;> simp
  have he := congrArg (fun v => f v i) hw
  simpa [join,split] using he.symm

def joinMap : (Two × Two) →ₗ[ℂ] Phi where
  toFun := join
  map_add' x y := by ext w i; simp [join,smul_add]; ring
  map_smul' c x := by ext w i; simp [join,smul_add,smul_smul]; ring

def equiv : (Two × Two) ≃ₗ[ℂ] Phi :=
  { joinMap with invFun := split, left_inv := split_join, right_inv := join_split }

def smRepresentation : Representation ℂ GaugeGroup (Two × Two) :=
  (twist weak (-3)).prod (twist weak 3)

theorem inverse_phase (g : GaugeGroup) (y : ℤ) : phase y g⁻¹ = phase (-y) g := by
  change (↑((g.2.2)⁻¹ ^ y):ℂ) = ↑(g.2.2^(-y))
  rw [inv_zpow,zpow_neg]

theorem split_equivariant (g : GaugeGroup) (f : Phi) :
    split (representation (hom g) f) = smRepresentation g (split f) := by
  apply Prod.ext
  · change left (hom g) (f (right (hom g)⁻¹ (Pi.single 0 1))) = _
    rw [← map_inv hom,right_basis]
    simp [split,smRepresentation,Representation.prod,twist,left_action,inverse_phase]
  · change left (hom g) (f (right (hom g)⁻¹ (Pi.single 1 1))) = _
    rw [← map_inv hom,right_basis]
    simp [split,smRepresentation,Representation.prod,twist,left_action,inverse_phase]

def admission : Representation.IntertwiningMap (representation.comp hom) smRepresentation :=
  equiv.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ split_equivariant

/-- Matrix entries used in the existing finite Phi action are evaluations of Hom coordinates. -/
theorem matrix_columns (m : Matrix (Fin 2) (Fin 2) ℂ) :
    split (Matrix.toLin' m) = (fun i => m i 0, fun i => m i 1) := by
  simp [split,Matrix.toLin'_apply,Matrix.mulVec_single]
  exact ⟨rfl,rfl⟩

theorem diagonal_vacuum (h1 h2 : ℂ) :
    split (Matrix.toLin' (ComponentAdmission.phiVEV h1 h2)) =
      (Pi.single 0 h1,Pi.single 1 h2) := by
  rw [matrix_columns]
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [ComponentAdmission.phiVEV]

theorem join_equivariant (g : GaugeGroup) (x : Two × Two) :
    representation (hom g) (join x) = join (smRepresentation g x) := by
  apply equiv.symm.injective
  change split (representation (hom g) (join x)) = split (join (smRepresentation g x))
  rw [split_equivariant,split_join,split_join]

def inclusion : Representation.IntertwiningMap smRepresentation (representation.comp hom) :=
  equiv.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun g x => (join_equivariant g x).symm)

end
end GUT.PatiSalam.PhiRepresentation
