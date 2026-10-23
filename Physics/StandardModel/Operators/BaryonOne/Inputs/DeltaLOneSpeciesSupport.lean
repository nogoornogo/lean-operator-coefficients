import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

/-! Arithmetic support of signed four-fermion species.
The hypotheses below are numerical necessary conditions; this file does not
assume or claim that their derivation from group invariance is already proved. -/
namespace Physics.DeltaLOneSpeciesSupport
set_option autoImplicit false

/-- Counts of physical fields followed by counts of their conjugates. -/
structure Counts where
  q : ℕ
  u : ℕ
  d : ℕ
  l : ℕ
  e : ℕ
  cq : ℕ
  cu : ℕ
  cd : ℕ
  cl : ℕ
  ce : ℕ
  deriving DecidableEq

def slotCount (n : Counts) : ℕ :=
  n.q + n.u + n.d + n.l + n.e + n.cq + n.cu + n.cd + n.cl + n.ce

def leptonDegree (n : Counts) : ℤ := n.l + n.e - n.cl - n.ce
def threeBaryonDegree (n : Counts) : ℤ := n.q + n.u + n.d - n.cq - n.cu - n.cd
def sixHypercharge (n : Counts) : ℤ :=
  n.q + 4 * n.u - 2 * n.d - 3 * n.l - 6 * n.e -
    n.cq - 4 * n.cu + 2 * n.cd + 3 * n.cl + 6 * n.ce
def leftSlots (n : Counts) : ℕ := n.q + n.l + n.cu + n.cd + n.ce

def duql : Counts := ⟨1,1,1,1,0,0,0,0,0,0⟩
def qque : Counts := ⟨2,1,0,0,1,0,0,0,0,0⟩
def qqql : Counts := ⟨3,0,0,1,0,0,0,0,0,0⟩
def duue : Counts := ⟨0,2,1,0,1,0,0,0,0,0⟩

/-- The two gauge-compatible candidates excluded by the Weyl action. -/
def antiQddL : Counts := ⟨0,0,0,1,0,1,0,2,0,0⟩
def antiDddE : Counts := ⟨0,0,0,0,1,0,0,3,0,0⟩

def GaugeAdmissible (n : Counts) : Prop :=
  slotCount n = 4 ∧ leptonDegree n = 1 ∧ sixHypercharge n = 0 ∧
    threeBaryonDegree n % 3 = 0

/-- Separate the gauge arithmetic from the genuinely Lorentz-theoretic exclusion. -/
theorem gauge_admissible_iff (n : Counts) : GaugeAdmissible n ↔
    n = duql ∨ n = qque ∨ n = qqql ∨ n = duue ∨ n = antiQddL ∨ n = antiDddE := by
  rcases n with ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩
  simp only [GaugeAdmissible, slotCount, leptonDegree, sixHypercharge,
    threeBaryonDegree, duql, qque, qqql, duue, antiQddL, antiDddE, Counts.mk.injEq]
  constructor
  · rintro ⟨hn, hl, hy, hb⟩
    have hB : (q : ℤ) + u + d - cq - cu - cd = -3 ∨
        (q : ℤ) + u + d - cq - cu - cd = 0 ∨
        (q : ℤ) + u + d - cq - cu - cd = 3 := by omega
    rcases hB with hB | hB | hB
    · have hz : q = 0 ∧ u = 0 ∧ d = 0 ∧ cl = 0 ∧ ce = 0 := by omega
      rcases hz with ⟨rfl,rfl,rfl,rfl,rfl⟩
      have he : e = 0 ∨ e = 1 := by omega
      rcases he with rfl | rfl
      · right; right; right; right; left; omega
      · right; right; right; right; right; omega
    · omega
    · have hz : cq = 0 ∧ cu = 0 ∧ cd = 0 ∧ cl = 0 ∧ ce = 0 := by omega
      rcases hz with ⟨rfl,rfl,rfl,rfl,rfl⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases hq with rfl | rfl | rfl | rfl
      · right; right; right; left; omega
      · left; omega
      · right; left; omega
      · right; right; left; omega
  · intro h
    rcases h with h | h | h | h | h | h <;> omega

theorem excluded_candidates_leftSlots :
    leftSlots antiQddL = 3 ∧ leftSlots antiDddE = 3 := by constructor <;> rfl

/-- This is an arithmetic predicate, not the definition of an invariant sector. -/
def Admissible (n : Counts) : Prop :=
  slotCount n = 4 ∧ leptonDegree n = 1 ∧ sixHypercharge n = 0 ∧
    threeBaryonDegree n % 3 = 0 ∧ leftSlots n % 2 = 0

theorem admissible_iff (n : Counts) : Admissible n ↔
    n = duql ∨ n = qque ∨ n = qqql ∨ n = duue := by
  rcases n with ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩
  simp only [Admissible, slotCount, leptonDegree, sixHypercharge,
    threeBaryonDegree, leftSlots, duql, qque, qqql, duue, Counts.mk.injEq]
  constructor
  · rintro ⟨hn, hl, hy, hb, hs⟩
    have hp : q + l + cu + cd + ce = 0 ∨ q + l + cu + cd + ce = 2 ∨
        q + l + cu + cd + ce = 4 := by omega
    have hB : (q : ℤ) + u + d - cq - cu - cd = -3 ∨
        (q : ℤ) + u + d - cq - cu - cd = 0 ∨
        (q : ℤ) + u + d - cq - cu - cd = 3 := by omega
    have hpos : (q : ℤ) + u + d - cq - cu - cd = 3 := by
      rcases hB with hB | hB | hB
      · rcases hp with hp | hp | hp <;> omega
      · omega
      · exact hB
    have hzero : cq = 0 ∧ cu = 0 ∧ cd = 0 ∧ cl = 0 ∧ ce = 0 := by omega
    rcases hzero with ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases hq with rfl | rfl | rfl | rfl <;> omega
  · intro h
    rcases h with h | h | h | h <;> omega

theorem baryonDegree_of_admissible (n : Counts) (h : Admissible n) :
    threeBaryonDegree n = 3 := by
  rcases (admissible_iff n).mp h with rfl | rfl | rfl | rfl <;> rfl

theorem no_conjugates (n : Counts) (h : Admissible n) :
    n.cq + n.cu + n.cd + n.cl + n.ce = 0 := by
  rcases (admissible_iff n).mp h with rfl | rfl | rfl | rfl <;> rfl

end Physics.DeltaLOneSpeciesSupport
