import Math.RepresentationTheory.Jets.DerivativeLiteratureHiggs

/-! Literal ordinary-derivative specialization of 2005.00008v3, Eq. (4.8).
Formal dagger labels are independent polynomial variables. -/
namespace Math.DerivativeLiteratureLiHiggs
set_option autoImplicit false
noncomputable section
open DerivativeLiteratureHiggs

def second (i j : Fin 4) : A := ∑ a : Fin 2, h true a*D i (D j (h false a))
def secondDual (i j : Fin 4) : A := ∑ a : Fin 2, D i (D j (h true a))*h false a
def l1 : A := rho*box (box rho)
def l2 : A := ∑ i : Fin 4, ∑ j : Fin 4,
  (metric i*metric j) • (second i j*secondDual i j)
def l3 : A := ∑ i : Fin 4, metric i • (rightCurrent i*box (leftCurrent i))

end
end Math.DerivativeLiteratureLiHiggs
