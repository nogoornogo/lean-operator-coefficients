import Math.RepresentationTheory.Jets.FiniteDerivativeCertificate
import Math.RepresentationTheory.Jets.DerivativeLiteratureScalar

/-! A proved actual source/basis and relation-row instance of the certificate. -/
namespace Math.FiniteDerivativeScalarControl
set_option autoImplicit false
noncomputable section
open ScalarJetQuadratic FiniteDerivativeCertificate

def coordinates : Source →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun p := ![p.val.coeff firstExponent,p.val.coeff secondExponent]
  map_add' p q := by funext i; fin_cases i <;> simp
  map_smul' c p := by funext i; fin_cases i <;> simp

theorem coordinates_first : coordinates first = ![1,0] := by
  funext i
  fin_cases i <;> simp [coordinates,first,exponents_ne]
theorem coordinates_second : coordinates second = ![0,1] := by
  funext i
  fin_cases i <;> simp [coordinates,second,Ne.symm exponents_ne]

def coordinateEquiv : Source ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toLinearMap := coordinates
  invFun c := c 0 • first+c 1 • second
  left_inv p := (source_reconstruct p).symm
  right_inv c := by
    change coordinates (c 0 • first+c 1 • second) = c
    rw [map_add,map_smul,map_smul,coordinates_first,coordinates_second]
    funext i
    fin_cases i <;> simp

def basis : Module.Basis (Fin 2) ℂ Source := Module.Basis.ofEquivFun coordinateEquiv

theorem basis_zero : basis 0 = first := by
  calc
    basis 0 = coordinateEquiv.symm (Pi.single 0 1) :=
      congrFun (Module.Basis.coe_ofEquivFun coordinateEquiv) 0
    _ = (1:ℂ) • first+0 • second := rfl
    _ = first := by simp
theorem basis_one : basis 1 = second := by
  calc
    basis 1 = coordinateEquiv.symm (Pi.single 1 1) :=
      congrFun (Module.Basis.coe_ofEquivFun coordinateEquiv) 1
    _ = (0:ℂ) • first+1 • second := rfl
    _ = second := by simp

def off : Presentation (ι := Fin 2) (κ := Unit) DerivativeLiteratureScalar.offInput where
  basis := basis
  relation _ := first+second
  relation_span := by
    rw [Set.range_const]
    exact relations_span.symm

theorem assemble_first (c : Fin 2 → ℂ) : off.assemble c first = c 0 := by
  have h := off.assemble_basis c 0
  change off.assemble c (basis 0) = c 0 at h
  rwa [basis_zero] at h
theorem assemble_second (c : Fin 2 → ℂ) : off.assemble c second = c 1 := by
  have h := off.assemble_basis c 1
  change off.assemble c (basis 1) = c 1 at h
  rwa [basis_one] at h

theorem off_rows_iff (c : Fin 2 → ℂ) : c ∈ off.rows ↔ c 0+c 1 = 0 := by
  constructor
  · intro hc
    have h := hc.1 ()
    change off.assemble c (first+second) = 0 at h
    simpa only [map_add,assemble_first,assemble_second] using h
  · intro hc
    constructor
    · intro k
      change off.assemble c (first+second) = 0
      rw [map_add,assemble_first,assemble_second,hc]
    · intro g i
      change off.assemble c (off.basis i) = c i
      exact off.assemble_basis c i

def on : Presentation (ι := Fin 2) (κ := Fin 2) DerivativeLiteratureScalar.onInput where
  basis := basis
  relation := basis
  relation_span := by
    rw [DerivativeLiteratureScalar.on_relations_top]
    exact basis.span_eq

theorem on_rows_zero (c : on.rows) : c = 0 := by
  apply Subtype.ext
  funext i
  have h := c.property.1 i
  change on.assemble c.val (on.basis i) = 0 at h
  rwa [on.assemble_basis] at h

end
end Math.FiniteDerivativeScalarControl
