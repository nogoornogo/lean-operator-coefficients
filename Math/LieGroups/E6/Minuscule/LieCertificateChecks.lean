import Math.LieGroups.E6.Minuscule.LieCertificateData
import Math.LieGroups.E6.Minuscule.D5Blocks
import Math.LieAlgebras.MatrixLieCertificate

/-!
# Kernel checks of the finite minuscule Lie certificates

Every check here reduces over integer data in Lean's kernel. The generating
Python programs are not trusted. These checks include the equality to the
actual pinned simple-root matrices, not just internal consistency of a table.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.
set_option Elab.async false

namespace Math.E6.Minuscule.LieChecks

open SparseMatrixCertificate MatrixLieCertificate LieData TauCeti.E6Minuscule

def e6GeneratorInt : Fin 12 → Matrix (Fin 27) (Fin 27) ℤ :=
  ![raisingMatrix 0, raisingMatrix 1, raisingMatrix 2, raisingMatrix 3,
    raisingMatrix 4, raisingMatrix 5, loweringMatrix 0, loweringMatrix 1,
    loweringMatrix 2, loweringMatrix 3, loweringMatrix 4, loweringMatrix 5]

def d5GeneratorInt : Fin 10 → Matrix (Fin 27) (Fin 27) ℤ :=
  ![raisingMatrix (d5Node 0), raisingMatrix (d5Node 1), raisingMatrix (d5Node 2),
    raisingMatrix (d5Node 3), raisingMatrix (d5Node 4), loweringMatrix (d5Node 0),
    loweringMatrix (d5Node 1), loweringMatrix (d5Node 2), loweringMatrix (d5Node 3),
    loweringMatrix (d5Node 4)]

theorem e6_actual_generators (i : Fin 12) : eval (e6Generators i) = e6GeneratorInt i := by
  fin_cases i <;> decide +kernel +revert

theorem d5_actual_generators (i : Fin 10) : eval (d5Generators i) = d5GeneratorInt i := by
  fin_cases i <;> decide +kernel +revert

def e6GeneratorIndex (i : Fin 12) : Fin 78 := ⟨i.val, by omega⟩
def d5GeneratorIndex (i : Fin 10) : Fin 45 := ⟨i.val, by omega⟩

theorem e6_generators_checked (i : Fin 12) :
    checkEq (e6Generators i) (e6Basis (e6GeneratorIndex i)) = true := by
  decide +kernel +revert

theorem d5_generators_checked (i : Fin 10) :
    checkEq (d5Generators i) (d5Basis (d5GeneratorIndex i)) = true := by
  decide +kernel +revert

theorem e6_provenance_checked (i : Fin 78) :
    checkOrigin e6Basis e6Generators e6Origin i = true := by
  decide +kernel +revert

theorem d5_provenance_checked (i : Fin 45) :
    checkOrigin d5Basis d5Generators d5Origin i = true := by
  decide +kernel +revert

theorem e6_closure_checked (i : Fin 12) (j : Fin 78) :
    checkEq (bracket (e6Generators i) (e6Basis j))
      (combination e6Basis (e6Closure i j)) = true := by
  fin_cases i <;> decide +kernel +revert

theorem d5_closure_checked (i : Fin 10) (j : Fin 45) :
    checkEq (bracket (d5Generators i) (d5Basis j))
      (combination d5Basis (d5Closure i j)) = true := by
  fin_cases i <;> decide +kernel +revert

theorem e6_scale_nonzero (i : Fin 78) : e6Scale i ≠ 0 := by decide +kernel +revert
theorem d5_scale_nonzero (i : Fin 45) : d5Scale i ≠ 0 := by decide +kernel +revert

theorem e6_pairing_checked (i j : Fin 78) :
    pairing (e6Dual i) (e6Basis j) = if i = j then e6Scale i else 0 := by
  fin_cases i <;> decide +kernel +revert

theorem d5_pairing_checked (i j : Fin 45) :
    pairing (d5Dual i) (d5Basis j) = if i = j then d5Scale i else 0 := by
  fin_cases i <;> decide +kernel +revert

end Math.E6.Minuscule.LieChecks
