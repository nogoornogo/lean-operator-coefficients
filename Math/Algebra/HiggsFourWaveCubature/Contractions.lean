import Math.Algebra.HiggsFourWaveCubature.Basic
import Math.RepresentationTheory.Color.Diagrams.ColoredWavePairing

/-! Exact metric channels and internal contraction values for ordered waves. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
open ColoredFourWavePolarization

def channel (r : Fin 3) (s t u v : Fin 4) : Fin 3 → GaussianInt := ![
  factor r*(5*gram r s t*gram r u v-gram r s u*gram r t v-gram r s v*gram r t u),
  factor r*(5*gram r s u*gram r t v-gram r s t*gram r u v-gram r s v*gram r t u),
  factor r*(5*gram r s v*gram r t u-gram r s t*gram r u v-gram r s u*gram r t v)]

theorem expected_channels (r : Fin 3) (s t u v i j k l : Fin 4) :
    expected r s t u v i j k l =
      channel r s t u v 0*metric i j*metric k l+
      channel r s t u v 1*metric i k*metric j l+
      channel r s t u v 2*metric i l*metric j k := by
  simp [channel,expected]
  ring

theorem channel_trace (r : Fin 3) (s t u v : Fin 4) :
    16*channel r s t u v 0+4*channel r s t u v 1+4*channel r s t u v 2 =
      72*factor r*gram r s t*gram r u v := by
  simp [channel]
  ring

def pairLabels : Fin 7 → Fin 4 → ColoredWavePairing.Label := ![
  ![(false,0),(false,0),(true,0),(true,0)],
  ![(false,0),(false,1),(true,0),(true,1)],
  ![(false,1),(false,1),(true,1),(true,1)],
  ![(false,0),(true,0),(false,0),(true,0)],
  ![(false,0),(true,0),(false,1),(true,1)],
  ![(false,1),(true,1),(false,1),(true,1)],
  ![(false,0),(true,1),(false,1),(true,0)]]
def KValue : Fin 3 → Fin 7 → ℤ := ![
  ![16,8,16,4,2,4,2],![16,8,16,8,0,8,8],![16,8,16,8,8,8,0]]
def KSum (r : Fin 3) (a : Fin 4 → ColoredWavePairing.Label) : GaussianInt :=
  ∑ p : Fin 24, (ColoredWavePairing.internalInt a p : GaussianInt)*
    gram r (assignments p 0) (assignments p 1)*gram r (assignments p 2) (assignments p 3)

theorem KSum_values : ∀ r : Fin 3, ∀ i : Fin 7,
    KSum r (pairLabels i) = 16*(KValue r i : GaussianInt) := by decide +kernel

end Math.HiggsFourWaveCubature
