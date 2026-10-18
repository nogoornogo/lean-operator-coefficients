import GUT.PatiSalam.Matching.ActionTranslation
import Physics.FieldTheory.Mass.ChiralActionConvention

/-! Selected restrictions of the full finite PS Yukawa index sums. No global
PS-equivariant branching map or vacuum-selection theorem is asserted. -/
namespace GUT.PatiSalam.SelectedPSYukawa
set_option autoImplicit false
noncomputable section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
abbrev Spin := Fin 2 → R
abbrev Fields := Fin 4 → Fin 2 → Spin (R := R)

def supported (a : Fin 4) (i : Fin 2) (s : Spin (R := R)) : Fields (R := R) :=
  Pi.single a (Pi.single i s)

def phiAction (y yt h1 h2 : ℂ) (l r : Fields (R := R)) : R :=
  ∑ a, ∑ i, ∑ j,
    (y*ComponentAdmission.phiVEV h1 h2 i j+
      yt*ComponentAdmission.conjugatePhiVEV h1 h2 i j) •
      GUT.ChiralActionConvention.barredLR (l a i) (r a j)

/- Selecting a component of the full sum derives its coefficient. -/
omit [StarModule ℂ R] in
theorem phi_selected (y yt h1 h2 : ℂ) (a : Fin 4) (i : Fin 2)
    (s : Spin (R := R)) (r : Fields (R := R)) :
    phiAction y yt h1 h2 (supported a i s) r =
      ComponentAdmission.diracEntry y yt h1 h2 i •
        GUT.ChiralActionConvention.barredLR s (r a i) := by
  classical
  have hzero (n : Spin (R := R)) : GUT.ChiralActionConvention.barredLR 0 n = 0 := by
    simp [GUT.ChiralActionConvention.barredLR]
  fin_cases a <;> fin_cases i <;>
    simp [phiAction,supported,Pi.single_apply,hzero,ComponentAdmission.phiVEV,
      ComponentAdmission.conjugatePhiVEV,ComponentAdmission.diracEntry,Fin.sum_univ_succ]

def chiAction (y : ℂ) (chi : ComponentAdmission.Array)
    (s : Spin (R := R)) (r : Fields (R := R)) : R :=
  ∑ a, ∑ i, (-(y*star (chi a i))) • GUT.ChiralActionConvention.barredLR s (r a i)

omit [StarModule ℂ R] in
theorem chi_selected (y z : ℂ) (a : Fin 4) (i : Fin 2)
    (s : Spin (R := R)) (r : Fields (R := R)) :
    chiAction y (Pi.single a (Pi.single i z)) s r =
      (-(y*star z)) • GUT.ChiralActionConvention.barredLR s (r a i) := by
  fin_cases a <;> fin_cases i <;> simp [chiAction,Fin.sum_univ_succ]

omit [StarModule ℂ R] in
theorem neutral_chi (y v : ℂ) (s : Spin (R := R)) (r : Fields (R := R)) :
    chiAction y (ComponentAdmission.neutralVEV v) s r =
      (-(y*star v)) • GUT.ChiralActionConvention.barredLR s (r 3 0) :=
  chi_selected y v 3 0 s r

omit [StarModule ℂ R] in
theorem colored_chi (y z : ℂ) (a : Fin 3) (s : Spin (R := R))
    (r : Fields (R := R)) :
    chiAction y (Pi.single a.castSucc (Pi.single 1 z)) s r =
      (-(y*star z)) • GUT.ChiralActionConvention.barredLR s (r a.castSucc 1) :=
  chi_selected y z a.castSucc 1 s r

theorem neutral_translation (p : ActionTranslation.Input) (s : Spin (R := R))
    (r : Fields (R := R))
    (h0 : star (s 0)*star (r 3 0 1) = -(star (r 3 0 1)*star (s 0)))
    (h1 : star (s 1)*star (r 3 0 0) = -(star (r 3 0 0)*star (s 1))) :
    star (chiAction p.yR (ComponentAdmission.neutralVEV (ActionTranslation.componentVEV p)) s r) =
      (-ActionTranslation.mixing p) • GUT.ChiralActionConvention.bracket s (r 3 0) := by
  rw [neutral_chi]
  exact ActionTranslation.translated_neutral p s (r 3 0) h0 h1

theorem phi_translation (p : ActionTranslation.Input) (s : Spin (R := R))
    (r : Fields (R := R))
    (h0 : star (s 0)*star (r 3 0 1) = -(star (r 3 0 1)*star (s 0)))
    (h1 : star (s 1)*star (r 3 0 0) = -(star (r 3 0 0)*star (s 1))) :
    star (phiAction p.yPhi 0 (p.w:ℂ) 0 (supported 3 0 s) r) =
      (-ActionTranslation.dirac p) • GUT.ChiralActionConvention.bracket s (r 3 0) := by
  rw [phi_selected]
  simp only [ComponentAdmission.diracEntry,ComponentAdmission.phiVEV,
    ComponentAdmission.conjugatePhiVEV,zero_mul,add_zero]
  exact ActionTranslation.translated_phi p s (r 3 0) h0 h1

end
end GUT.PatiSalam.SelectedPSYukawa
