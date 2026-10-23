import Math.Algebra.Waves.FourWaveEvaluation

/-! Square-free polarization of four linear waves; all identities are algebraic. -/
namespace Math.FourWavePolarization
set_option autoImplicit false
noncomputable section
open MvPolynomial FourWaveEvaluation

def permanent {R : Type*} [CommRing R] (a b c d : Fin 4 → R) : R :=
  a 0*b 1*c 2*d 3 +
  a 0*b 1*c 3*d 2 +
  a 0*b 2*c 1*d 3 +
  a 0*b 2*c 3*d 1 +
  a 0*b 3*c 1*d 2 +
  a 0*b 3*c 2*d 1 +
  a 1*b 0*c 2*d 3 +
  a 1*b 0*c 3*d 2 +
  a 1*b 2*c 0*d 3 +
  a 1*b 2*c 3*d 0 +
  a 1*b 3*c 0*d 2 +
  a 1*b 3*c 2*d 0 +
  a 2*b 0*c 1*d 3 +
  a 2*b 0*c 3*d 1 +
  a 2*b 1*c 0*d 3 +
  a 2*b 1*c 3*d 0 +
  a 2*b 3*c 0*d 1 +
  a 2*b 3*c 1*d 0 +
  a 3*b 0*c 1*d 2 +
  a 3*b 0*c 2*d 1 +
  a 3*b 1*c 0*d 2 +
  a 3*b 1*c 2*d 0 +
  a 3*b 2*c 0*d 1 +
  a 3*b 2*c 1*d 0

theorem map_permanent {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c d : Fin 4 → R) :
    f (permanent a b c d) =
      permanent (f ∘ a) (f ∘ b) (f ∘ c) (f ∘ d) := by
  simp only [permanent,map_add,map_mul,Function.comp_apply]

def linear (u : Fin 4 → ℂ) : P := ∑ i : Fin 4, u i • X i

@[simp] theorem pderiv_linear (s : Fin 4) (u : Fin 4 → ℂ) :
    pderiv s (linear u) = C (u s) := by
  classical
  simp [linear,MvPolynomial.smul_eq_C_mul,Pi.single_apply]

theorem coefficient_derivatives (p : P) :
    coefficient p = constantCoeff (pderiv 0 (pderiv 1 (pderiv 2 (pderiv 3 p)))) := by
  change p.coeff squareFree = (pderiv 0 (pderiv 1 (pderiv 2 (pderiv 3 p)))).coeff 0
  simp [coeff_pderiv,squareFree,Fin.sum_univ_succ]
  apply congrArg p.coeff
  ext i
  simp only [Finsupp.add_apply]
  omega

theorem coefficient_product (a b c d : Fin 4 → ℂ) :
    coefficient (linear a*linear b*linear c*linear d) = permanent a b c d := by
  rw [coefficient_derivatives]
  simp only [pderiv_mul,map_add,pderiv_linear,pderiv_C,zero_mul,mul_zero,
    zero_add,add_zero]
  simp only [map_add,map_mul,constantCoeff_C,permanent]
  ring

/-- Square-free wave value of each of the five derivative partitions. -/
def moment {R : Type*} [CommRing R] (k : Fin 4 → Fin 4 → R)
    (r : Fin 5) (a b c d : Fin 4) : R := match r with
  | 0 => permanent (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun s => k s a*k s b*k s c*k s d)
  | 1 => permanent (fun _ => 1) (fun _ => 1)
      (fun s => k s a*k s b*k s c) (fun s => k s d)
  | 2 => permanent (fun _ => 1) (fun _ => 1)
      (fun s => k s a*k s b) (fun s => k s c*k s d)
  | 3 => permanent (fun _ => 1) (fun s => k s a*k s b)
      (fun s => k s c) (fun s => k s d)
  | 4 => permanent (fun s => k s a) (fun s => k s b)
      (fun s => k s c) (fun s => k s d)

theorem map_moment {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (k : Fin 4 → Fin 4 → R) (r : Fin 5) (a b c d : Fin 4) :
    f (moment k r a b c d) = moment (fun s i => f (k s i)) r a b c d := by
  fin_cases r <;> simp only [moment,permanent,map_add,map_mul,map_one]

end
end Math.FourWavePolarization
