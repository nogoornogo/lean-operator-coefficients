import GUT.PatiSalam.Matching.NeutralMass

/-! Exact restrictions of the displayed finite component contraction.
No PS group equivariance or two-component charge-conjugation adapter is supplied. -/
namespace GUT.PatiSalam.ComponentAdmission
set_option autoImplicit false
noncomputable section
abbrev Array := Fin 4 → Fin 2 → ℂ

def contraction (chi f : Array) : ℂ := ∑ a, ∑ i, star (chi a i) * f a i

theorem contraction_expansion (chi f : Array) : contraction chi f =
    star (chi 0 0)*f 0 0 + star (chi 0 1)*f 0 1 +
    star (chi 1 0)*f 1 0 + star (chi 1 1)*f 1 1 +
    star (chi 2 0)*f 2 0 + star (chi 2 1)*f 2 1 +
    star (chi 3 0)*f 3 0 + star (chi 3 1)*f 3 1 := by
  simp [contraction, Fin.sum_univ_succ]
  ring

def neutralVEV (v : ℂ) : Array := Pi.single 3 (Pi.single 0 v)

theorem neutral_restriction (v : ℂ) (f : Array) :
    contraction (neutralVEV v) f = star v * f 3 0 := by
  simp [contraction, neutralVEV, Fin.sum_univ_succ]

/-- Vertex and mixing use the same coupling in the literal component convention. -/
theorem yukawa_neutral (y v : ℂ) (f : Array) :
    -y * contraction (neutralVEV v) f = -(y*star v) * f 3 0 := by
  rw [neutral_restriction]
  ring

/-- This is the explicit holomorphic symmetric action for the supplied mass chart.
Its identification with mixed four-component source notation is not asserted. -/
def symmetricAction (d M mu : ℂ) (x : Fin 3 → ℂ) : ℂ :=
  -(∑ i, ∑ j, x i * NeutralMass.mass d M mu i j * x j) / 2

theorem symmetric_action (d M mu : ℂ) (x : Fin 3 → ℂ) :
    symmetricAction d M mu x =
      -(d*x 0*x 1 + M*x 1*x 2 + mu/2*x 2*x 2) := by
  simp [symmetricAction, NeutralMass.mass, Fin.sum_univ_succ]
  ring

/-- Keep both diagonal Phi directions until a vacuum is selected. -/
def phiVEV (h1 h2 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![h1,0;0,h2]
def conjugatePhiVEV (h1 h2 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star h2,0;0,star h1]

/-- The diagonal restriction of tau2 * conjugate(Phi) * tau2. -/
theorem conjugate_phi (h1 h2 : ℂ) :
    (!![0,-Complex.I;Complex.I,0] : Matrix (Fin 2) (Fin 2) ℂ) *
      (phiVEV h1 h2).map star * !![0,-Complex.I;Complex.I,0] =
      conjugatePhiVEV h1 h2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, phiVEV, conjugatePhiVEV, Fin.sum_univ_succ]
    <;> ring_nf <;> simp [Complex.I_sq]

def diracEntry (y yt h1 h2 : ℂ) (i : Fin 2) : ℂ :=
  y * phiVEV h1 h2 i i + yt * conjugatePhiVEV h1 h2 i i

theorem up_neutrino_entry (y yt h1 h2 : ℂ) :
    diracEntry y yt h1 h2 0 = y*h1 + yt*star h2 := rfl

theorem down_lepton_entry (y yt h1 h2 : ℂ) :
    diracEntry y yt h1 h2 1 = y*h2 + yt*star h1 := rfl

/-- Selecting h2=0 still retains the second conjugate Yukawa direction. -/
theorem selected_entries (y yt h : ℂ) :
    diracEntry y yt h 0 0 = y*h ∧ diracEntry y yt h 0 1 = yt*star h := by
  simp [diracEntry, phiVEV, conjugatePhiVEV]

/-- Six times hypercharge from the supplied B-L and T3R eigenvalue dictionary. -/
def sixY (a : Fin 4) (i : Fin 2) : ℤ :=
  (if a = 3 then -3 else 1) + (if i = 0 then 3 else -3)

theorem colored_charges (a : Fin 3) :
    sixY (Fin.castSucc a) 0 = 4 ∧ sixY (Fin.castSucc a) 1 = -2 := by
  fin_cases a <;> decide

theorem lepton_charges : sixY 3 0 = 0 ∧ sixY 3 1 = -6 := by decide

theorem neutral_vev_charge : sixY 3 0 = 0 := by decide

theorem yukawa_charge (a : Fin 4) (i : Fin 2) :
    -sixY a i + sixY a i = 0 := by ring

end
end GUT.PatiSalam.ComponentAdmission
